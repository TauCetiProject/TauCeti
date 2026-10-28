import VersoBlog

open Verso Genre Blog Output Html

namespace Site.Blog.QualityIndicators

private def resultsTable (label : String) (columns : Array String)
    (rows : Array (Array Html)) : Html := {{
  <div class="blog-table" tabindex="0" role="region" aria-label={{label}}>
    <table>
      <thead><tr>{{columns.map fun column => {{<th scope="col">{{Html.text true column}}</th>}}}}</tr></thead>
      <tbody>{{rows.map fun row => {{
        <tr>{{row.mapIdx fun i cell =>
          if i == 0 then {{<th scope="row">{{cell}}</th>}} else {{<td>{{cell}}</td>}}}}</tr>
      }}}}</tbody>
    </table>
  </div>
}}

private def unnecessaryHypotheses : Html := resultsTable "Unnecessary hypotheses"
  #["Library", "Opus", "Sonnet"] #[
    #[{{"Mathlib"}}, {{"31/1,000 · "<strong>"3.1%"</strong>" [2.2%, 4.4%]"}}, {{"6/300 · "<strong>"2.0%"</strong>" [0.9%, 4.3%]"}}],
    #[{{"Tau Ceti"}}, {{"68/1,000 · "<strong>"6.8%"</strong>" [5.4%, 8.5%]"}}, {{"12/300 · "<strong>"4.0%"</strong>" [2.3%, 6.9%]"}}],
    #[{{"Formal Frontier"}}, {{"34/1,000 · "<strong>"3.4%"</strong>" [2.4%, 4.7%]"}}, {{"12/300 · "<strong>"4.0%"</strong>" [2.3%, 6.9%]"}}],
    #[{{"Lean Pool"}}, {{"150/1,000 · "<strong>"15.0%"</strong>" [12.9%, 17.3%]"}}, {{"39/300 · "<strong>"13.0%"</strong>" [9.7%, 17.3%]"}}],
    #[{{"Anthropic FLT"}}, {{"203/1,000 · "<strong>"20.3%"</strong>" [17.9%, 22.9%]"}}, {{"52/300 · "<strong>"17.3%"</strong>" [13.5%, 22.0%]"}}],
    #[{{"OpenAI Math"}}, {{"17/100 · "<strong>"17.0%"</strong>" [10.9%, 25.5%]"}}, {{"48/300 · "<strong>"16.0%"</strong>" [12.3%, 20.6%]"}}],
    #[{{"AxiomMath CFSG"}}, {{"—"}}, {{"70/300 · "<strong>"23.3%"</strong>" [18.9%, 28.4%]"}}]
  ]

private def mathlibDuplicates : Html := resultsTable "Results already available in Mathlib"
  #["Library", "Opus", "Sonnet"] #[
    #[{{"Tau Ceti"}}, {{"50/1,000 · "<strong>"5.0%"</strong>" [3.8%, 6.5%]"}}, {{"35/1,000 · "<strong>"3.5%"</strong>" [2.5%, 4.8%]"}}],
    #[{{"Formal Frontier"}}, {{"46/1,000 · "<strong>"4.6%"</strong>" [3.5%, 6.1%]"}}, {{"45/1,000 · "<strong>"4.5%"</strong>" [3.4%, 6.0%]"}}],
    #[{{"Lean Pool"}}, {{"68/1,000 · "<strong>"6.8%"</strong>" [5.4%, 8.5%]"}}, {{"58/1,000 · "<strong>"5.8%"</strong>" [4.5%, 7.4%]"}}],
    #[{{"Anthropic FLT"}}, {{"137/1,000 · "<strong>"13.7%"</strong>" [11.7%, 16.0%]"}}, {{"118/1,000 · "<strong>"11.8%"</strong>" [9.9%, 13.9%]"}}],
    #[{{"OpenAI Math"}}, {{"1/100 · "<strong>"1.0%"</strong>" [0.2%, 5.4%]"}}, {{"8/300 · "<strong>"2.7%"</strong>" [1.4%, 5.2%]"}}],
    #[{{"AxiomMath CFSG"}}, {{"—"}}, {{"15/300 · "<strong>"5.0%"</strong>" [3.1%, 8.1%]"}}]
  ]

private def repeatedProofs : Html := resultsTable "Repeated proof machinery in a file"
  #["Library", "Sonnet"] #[
    #[{{"Mathlib"}}, {{"60/372 · "<strong>"16.1%"</strong>" [12.7%, 20.2%]"}}],
    #[{{"Tau Ceti"}}, {{"64/372 · "<strong>"17.2%"</strong>" [13.7%, 21.4%]"}}],
    #[{{"Formal Frontier"}}, {{"128/372 · "<strong>"34.4%"</strong>" [29.8%, 39.4%]"}}],
    #[{{"Lean Pool"}}, {{"180/372 · "<strong>"48.4%"</strong>" [43.4%, 53.5%]"}}],
    #[{{"Anthropic FLT"}}, {{"189/372 · "<strong>"50.8%"</strong>" [45.7%, 55.9%]"}}],
    #[{{"OpenAI Math"}}, {{"154/372 · "<strong>"41.4%"</strong>" [36.5%, 46.5%]"}}],
    #[{{"AxiomMath CFSG"}}, {{"162/300 · "<strong>"54.0%"</strong>" [48.3%, 59.6%]"}}]
  ]

end Site.Blog.QualityIndicators

open Site.Blog.QualityIndicators

#doc (Post) "Simple quality indicators for Lean libraries" =>

%%%
authors := ["Kim Morrison", "Remy Degenne"]
date := {year := 2026, month := 10, day := 28}
%%%

Kim Morrison and Remy Degenne did an audit of a few formalization quality indicators across several Lean libraries. Our purpose was to see if we could quantify the common assumption that Mathlib is a high-quality library, while AI-generated formalizations perhaps less so, and to see if efforts to improve the quality of AI-generated formalizations could be measured.

There are many aspects of quality, and some are captured by mechanical checks like linters, or by community norms like Comparator challenges and formalization.yaml, or more diffuse social factors (is the repository maintained? Are people engaging with it?). We focused on a set of simple questions about individual theorems or files that can be assessed by AI judges. The indicators we used include:
1) does a theorem have hypotheses that could be removed? (not weakened, but completely removed)
2) is a theorem a duplicate or one-line consequence of something in Mathlib?
3) are there parts of proofs that appear several times in a file and could be turned into lemmas?

We evaluated Mathlib, Tau Ceti, Formal Frontier, Lean Pool, Anthropic's FLT, OpenAI's mathematical corpus and Axiom's CFSG proof (with more partial results for the last two).

For each of the indicators, we sample randomly theorems (for the first two) or files (for the third one) from the library, and ask an AI judge to answer the question. We then compute the percentage of theorems/files that are flagged by the AI judge, and also report 95% confidence intervals for the true rate.
We found that the exact percentages depend on the AI model used (more expensive models report more issues), but that the groups and relative gaps are consistent across models.

The results in the tables below confirm the assumption that Mathlib is high-quality, show that Tau Ceti and Formal Frontier are not far behind on those metrics, and that the other libraries have generally higher percentages of flagged entries (although the OpenAI corpus has a very low rate of Mathlib duplicates).
Tau Ceti and Formal Frontier are actively trying to take the lessons learned in Mathlib to guide the AI formalization process, and our takeaway from the results is that those efforts, while not perfect, are paying off.

The indicators we looked at are very partial (they do not measure anything about the quality of definitions, for a start), but they are easy to compute and give a preliminary signal. We would love to turn this into a more systematic audit. We have inference to run the evaluations but little time to further develop the methodology. If you are interested in helping, please reach out to us.


# Results

Note: the OpenAI Math and AxiomMath CFSG results have higher uncertainty because of smaller sample sizes. Those results will be updated.

- Unnecessary hypotheses:

Sample theorems uniformly at random, and ask whether any of the hypotheses could be removed without changing the statement of the theorem. Assumptions that can be weakened do not count: they need to be entirely removed.

:::blob unnecessaryHypotheses
:::

Mathlib, Formal Frontier and Tau Ceti have low rates of unnecessary hypotheses, while other libraries have a higher rates.

- Results already available in Mathlib:

Sample theorems uniformly at random, and ask whether the theorem is already in Mathlib, or is a one-line consequence of a theorem in Mathlib.

:::blob mathlibDuplicates
:::

OpenAI Math did a very good job of avoiding duplicates with Mathlib, while Anthropic FLT has a notably high rate of duplicates which seems mostly due to a frequent use of abbreviations for special cases of Mathlib declarations, about which lemmas are then re-proven. The other libraries are in between.

- Repeated proof machinery in a file:

Sample files uniformly at random, and ask whether there are parts of proofs that appear several times in the file and could be turned into lemmas.

:::blob repeatedProofs
:::

Mathlib and Tau Ceti have the lowest duplication rates, Formal Frontier is in the middle, and the other libraries have higher rates.

We started testing other models, and did a few second passes to check the flags, but lots of work remains.
All the results, prompts and other details are available in the [lean-quality-indicators repository](https://github.com/RemyDegenne/lean-quality-indicators).
