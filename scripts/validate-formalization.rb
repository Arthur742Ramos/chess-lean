#!/usr/bin/env ruby
# frozen_string_literal: true

require "optparse"
require "yaml"

module FormalizationTemplate
  SENTINEL = /\ATEMPLATE(?::|\z)/
  REQUIRED_LICENSE = "Apache-2.0"
  REQUIRED_SECTIONS = %w[project classification automation review].freeze
  SOURCE_RELATIONSHIPS = %w[
    formalizes
    adapts
    independently-proves
    background
    other
  ].freeze
  SOURCE_TYPES = %w[
    paper
    book
    web discussion
    folklore
    original-proof
    other
  ].freeze
  RELATED_FORMALIZATION_RELATIONSHIPS = %w[
    builds-on
    adapts
    independent
    supersedes
    other
  ].freeze
  AUTHOR_ENDORSEMENTS = %w[
    participated
    endorsed
    no-response
    not-contacted
    declined
    n/a
    other
  ].freeze
  EXPECTED_TEMPLATE_PATHS = [
    "$.project.name",
    "$.project.description",
    "$.project.authors[0]",
    "$.project.responsible_maintainers[0]",
    "$.classification.arxiv[0]",
    "$.classification.msc2020[0]",
    "$.sources[0].title",
    "$.sources[0].authors[0]",
    "$.sources[0].contributors[0].name",
    "$.sources[0].contributors[0].role",
    "$.sources[0].id",
    "$.sources[0].type",
    "$.sources[0].location",
    "$.sources[0].relationship",
    "$.sources[0].note",
    "$.sources[0].license",
    "$.sources[0].author_endorsement",
    "$.related_formalizations[0].id",
    "$.related_formalizations[0].relationship",
    "$.related_formalizations[0].note",
    "$.status.scope",
    "$.status.sorry_count",
    "$.status.sorry_in_definitions",
    "$.status.axioms[0]",
    "$.automation.methods[0].method",
    "$.automation.methods[0].models[0]",
    "$.automation.methods[0].framework",
    "$.automation.methods[0].tool_setup",
    "$.automation.methods[0].cost.wall_time",
    "$.automation.methods[0].cost.spend_usd",
    "$.automation.methods[0].cost.hardware",
    "$.automation.methods[0].prompting_notes",
    "$.automation.spend_usd",
    "$.automation.notes",
    "$.fidelity.divergences",
    "$.review.status",
    "$.review.reviewers[0]",
    "$.review.notes",
    "$.alignment.namespace",
    "$.alignment.statements[0].source",
    "$.alignment.statements[0].lean",
    "$.alignment.statements[0].module",
    "$.alignment.statements[0].status",
    "$.alignment.statements[0].note",
    "$.acknowledgements"
  ].freeze

  class ValidationError < StandardError; end

  def self.load_document(path)
    text = File.binread(path).force_encoding(Encoding::UTF_8)
    raise ValidationError, "#{path} must be valid UTF-8" unless text.valid_encoding?

    document = YAML.safe_load(
      text,
      permitted_classes: [],
      permitted_symbols: [],
      aliases: false
    )
    raise ValidationError, "#{path} must contain one top-level mapping" unless document.is_a?(Hash)

    missing = REQUIRED_SECTIONS.reject { |section| document[section].is_a?(Hash) }
    unless missing.empty?
      raise ValidationError,
            "#{path} must contain the required mapping sections: #{missing.join(', ')}"
    end

    document
  rescue Psych::Exception => error
    detail = error.message.lines.first&.strip
    raise ValidationError, "cannot parse #{path} as YAML: #{detail}"
  rescue SystemCallError => error
    raise ValidationError, "cannot read #{path}: #{error.message}"
  end

  def self.placeholder_paths(value, path = "$")
    case value
    when Hash
      value.flat_map do |key, child|
        placeholder_paths(child, "#{path}.#{key}")
      end
    when Array
      value.each_with_index.flat_map do |child, index|
        placeholder_paths(child, "#{path}[#{index}]")
      end
    when String
      value.lstrip.match?(SENTINEL) ? [path] : []
    else
      []
    end
  end

  def self.validate_portable_provenance(document, path)
    sources = document["sources"]
    if sources.is_a?(Array)
      sources.each_with_index do |source, index|
        next unless source.is_a?(Hash)

        relationship = source["relationship"]
        unless relationship.nil? || SOURCE_RELATIONSHIPS.include?(relationship)
          raise ValidationError,
                "#{path} $.sources[#{index}].relationship must use a canonical " \
                "Palomar value: #{SOURCE_RELATIONSHIPS.join(', ')}"
        end

        type = source["type"]
        unless type.nil? || SOURCE_TYPES.include?(type)
          raise ValidationError,
                "#{path} $.sources[#{index}].type must use a canonical Palomar value: " \
                "#{SOURCE_TYPES.join(', ')}"
        end

        endorsement = source["author_endorsement"]
        unless endorsement.nil? || AUTHOR_ENDORSEMENTS.include?(endorsement)
          raise ValidationError,
                "#{path} $.sources[#{index}].author_endorsement must use a canonical " \
                "Palomar value: #{AUTHOR_ENDORSEMENTS.join(', ')}"
        end
      end
    end

    related = document["related_formalizations"]
    return unless related.is_a?(Array)

    related.each_with_index do |item, index|
      next unless item.is_a?(Hash)

      relationship = item["relationship"]
      unless relationship.nil? || RELATED_FORMALIZATION_RELATIONSHIPS.include?(relationship)
        raise ValidationError,
              "#{path} $.related_formalizations[#{index}].relationship must use a canonical " \
              "Palomar value: #{RELATED_FORMALIZATION_RELATIONSHIPS.join(', ')}"
      end
    end
  end

  def self.validate(path, expect_template: false)
    document = load_document(path)
    unless document["version"] == "v0.4"
      raise ValidationError,
            "#{path} $.version must be \"v0.4\", not #{document["version"].inspect}"
    end
    actual_license = document.dig("project", "license")
    unless actual_license == REQUIRED_LICENSE
      raise ValidationError, <<~MESSAGE.chomp
        #{path} $.project.license must be #{REQUIRED_LICENSE.inspect}, not #{actual_license.inspect}.
        Keep the repository's Apache-2.0 LICENSE file unchanged and set project.license to #{REQUIRED_LICENSE.inspect}.
      MESSAGE
    end
    description = document.dig("project", "description")
    unless description.is_a?(String) && !description.strip.empty? && description.strip.length <= 10_000
      raise ValidationError,
            "#{path} $.project.description must be nonempty text of at most 10000 characters"
    end

    placeholders = placeholder_paths(document)
    if expect_template
      missing = EXPECTED_TEMPLATE_PATHS - placeholders
      unexpected = placeholders - EXPECTED_TEMPLATE_PATHS
      return placeholders if missing.empty? && unexpected.empty?

      details = []
      details << "missing expected values: #{missing.join(', ')}" unless missing.empty?
      details << "unexpected values: #{unexpected.join(', ')}" unless unexpected.empty?
      raise ValidationError,
            "#{path} does not have the expected TEMPLATE sentinel surface; #{details.join('; ')}"
    end

    validate_portable_provenance(document, path)

    return placeholders if placeholders.empty?

    locations = placeholders.map { |item| "  #{item}" }.join("\n")
    raise ValidationError, <<~MESSAGE.chomp
      #{path} still contains #{placeholders.length} TEMPLATE value(s):
      #{locations}
      Replace every listed value with project-specific metadata; use [] for a placeholder list where the honest answer is none.
    MESSAGE
  end

  def self.run_cli(arguments, output: $stdout, errors: $stderr)
    expect_template = false
    parser = OptionParser.new do |options|
      options.banner = "Usage: #{File.basename($PROGRAM_NAME)} [--expect-template] [formalization.yaml]"
      options.on(
        "--expect-template",
        "require the canonical template's exact TEMPLATE sentinel surface"
      ) { expect_template = true }
    end
    remaining = parser.parse(arguments)
    raise OptionParser::InvalidArgument, "expected at most one metadata path" if remaining.length > 1

    path = remaining.fetch(0, "formalization.yaml")
    placeholders = validate(path, expect_template: expect_template)
    if expect_template
      output.puts "#{path} contains the expected #{placeholders.length} TEMPLATE values"
    else
      output.puts "#{path} contains no TEMPLATE values"
    end
    0
  rescue OptionParser::ParseError => error
    errors.puts error.message
    errors.puts parser
    2
  rescue ValidationError => error
    errors.puts error.message
    1
  end
end

exit FormalizationTemplate.run_cli(ARGV) if $PROGRAM_NAME == __FILE__
