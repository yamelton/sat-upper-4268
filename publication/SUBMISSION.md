# Submission handoff

## Author and account information

- Author: **Fedor Vorobyev** (Фёдор Воробьёв).
- Contact: **fedorvorobev@gmail.com**.
- Affiliation: none; enter **Independent** where arXiv registration asks for one.
- Residence, if needed: Belgrade, Serbia.
- Academic background, if needed for a profile: Candidate of Physical and
  Mathematical Sciences; Faculty of Computational Mathematics and Cybernetics,
  Lomonosov Moscow State University. Do not add a current MSU or Yandex affiliation.
- GitHub: `yamelton`, explicitly authorized by the author for this publication.
- Primary category: **math.PR**. Requested cross-list: **cs.DM**.
- Manuscript license: **arXiv.org perpetual, non-exclusive license 1.0**.

## arXiv

1. [Register](https://arxiv.org/user/register) and verify your email. Keep
   passwords and email verification steps in your browser.
2. Start a new submission as an author and select math.PR. Follow the
   [endorsement instructions](https://info.arxiv.org/help/endorsement.html)
   to obtain your request link/code. A colleague must be eligible in the
   relevant endorsement domain; eligibility is not implied by a job title.
3. If the endorsement gate permits uploading, upload
   `dist/sat-upper-4268-arxiv.zip`. Choose PDFLaTeX and `main.tex`.
   The ZIP includes the generated `main.bbl`; upload source rather than
   only the PDF.
4. Use `publication/metadata.json` for title, author, abstract, category,
   and comments. The license is the arXiv distribution license, not the
   Apache software license.
5. Inspect arXiv's compiled PDF, metadata, and links. Leave the draft at the
   furthest permitted stage until endorsement and author review are complete.
   An uploaded draft is not a submitted or announced article.

If uploading is blocked before endorsement, the validated archive and
metadata remain ready for upload. Record the actual account/draft status
privately; never commit passwords, tokens, or the endorsement code.

## Software archive and DOI

Sign in to [Zenodo](https://zenodo.org) using the authorized GitHub account.
For this mixed software/manuscript repository, upload the **software-only**
ZIP from the release manually rather than applying one software license to
an automatic archive containing the paper.

Use resource type Software, version 1.0.0, creator **Vorobyev, Fedor**,
license **Apache License 2.0**, and the description in `.zenodo.json`.
Include the exact release URL as a related resource. Reserve a DOI in the
draft if available, inspect the files and metadata, then publish the software
record. Return the record URL/DOI so it can be added to the paper and citation
metadata. A reserved DOI is not yet a published archive.

An ORCID can be created at [orcid.org/register](https://orcid.org/register)
and linked to both records; it is optional for the prepared artifact.

## Colleague-facing endorsement request

Subject: arXiv endorsement request for a random 3-SAT paper

I'm preparing a paper proving that a random signed 3-CNF formula with
floor(4.268 n) independent clauses is unsatisfiable with probability tending
to one. The paper gives a self-contained argument based on clause/site
comparison, together with a complete Lean formalization and an exact
rational certificate.

The paper and code are available at:
https://github.com/yamelton/sat-upper-4268/releases

Would you be willing to endorse my first submission in math.PR, if you are
eligible in that domain? I can forward arXiv's endorsement request email.

Thank you,
Fedor Vorobyev

This draft has not been sent. Forward the actual endorsement request
separately, keeping the private code out of the public repository.

## Future journal publication

The paper retains its copyright and uses arXiv's limited non-exclusive
distribution license. The software license does not cover the manuscript.
Preprint posting is not a promise of journal acceptance, but it is compatible
with the following candidate routes:

- **Journal of Statistical Physics**: a natural methodological connection
  to the interpolation literature. Springer Nature's
  [preprint policy](https://support.springernature.com/en/support/solutions/articles/6000258807-preprints)
  permits preprints. Its [author instructions](https://link.springer.com/journal/10955/submission-guidelines)
  require a clear contribution and appropriate disclosure of substantive AI use.
- **Combinatorics, Probability and Computing**: its
  [scope](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/information/author-instructions)
  includes random combinatorial structures and probabilistic methods.
  Check its linked current preprint, publishing-agreement, and open-access
  options before selecting it; no journal submission is made this weekend.

Recheck the selected journal's actual policy before submission. Supply the
arXiv link as a preprint, and keep the journal-formatted version distinct
from the author's preprint. Funding, conflicts, and the full scope of AI
assistance must be stated accurately by the author when a journal requests them.
