/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.FixedField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

/-!
# The kernel of an isogeny

An isogeny is a map of function fields, so it has no point map to take a fibre of. Its kernel is
read off the translation action instead: a point `P` of `W₁` lies in the kernel exactly when
translating by `P` moves no function pulled back from `W₂`. On the points where the two notions
can be compared this is the usual kernel, since `φ(X + P) = φ(X) + φ(P)`, and it is stated here
for every isogeny over every field, with no separability or rationality hypothesis.

The degree bounds the kernel: a pulled-back field of degree `d` is fixed by at most `d`
translations. The bound is often strict, because these are the `F`-rational points only: a
separable isogeny whose geometric kernel is not rational has fewer of them than its degree.
Equality needs separability *and* rationality of the whole geometric kernel. For `1 − π_q` over a
finite field both hold, its geometric kernel being the `𝔽_q`-rational points, and the point count
`deg (1 − π_q) = #E(𝔽_q)` is what they then yield; neither that identity nor the general equality
is proved here.

## Main definitions

* `TauCeti.Isogeny.ker`: the subgroup of points whose translation fixes the pulled-back field.

## Main results

* `TauCeti.Isogeny.card_ker_le_degree`: the kernel has at most `deg φ` elements.
* `TauCeti.Isogeny.ker_le_ker_comp`: postcomposition can only enlarge the kernel.
* `TauCeti.Isogeny.ker_eq_bot_of_separableDegree_eq_one`: separable degree one forces this kernel
  to be trivial, as for Frobenius.
* `TauCeti.Isogeny.card_ker_eq_degree_iff`: the cardinality statement is *equivalent* to the
  reverse fixed-field inclusion.
* `TauCeti.Isogeny.card_ker_eq_degree_of_forall_exists_translation` and
  `card_ker_eq_degree_iff_isGalois_and_forall_exists_translation`: it holds exactly when the
  function field is Galois over the pulled-back field and every automorphism over that field is a
  translation, so those two conditions are what remains of the identity.
* `TauCeti.Isogeny.card_ker_dvd_separableDegree` and `card_ker_le_separableDegree`: the kernel
  order divides, so is bounded by, the separable degree.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) proves the corresponding cardinality statement in
`EC/SeparableKernelTorsor.lean` as `card_kernel_eq_degree_of_separable_isogeny`, parametric on two
witnesses. The second exists only because its isogeny carries a point map independent of the
function-field pullback, so separability and the kernel are a priori unrelated there. The kernel
here is defined from the pullback, so that witness has no counterpart.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]

/-- **The kernel of an isogeny**: the points whose translation fixes every pulled-back function. -/
noncomputable def ker (φ : Isogeny W₁ W₂) : AddSubgroup (W₁⁄F).toAffine.Point :=
  translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- The defining equation of `ker`. -/
theorem ker_def (φ : Isogeny W₁ W₂) :
    φ.ker = translationFixingSubgroup W₁ φ.fieldPullback.fieldRange := (rfl)

/-- **A point is in the kernel exactly when it translates every pulled-back function to
itself.** -/
@[simp]
theorem mem_ker_iff {φ : Isogeny W₁ W₂} {P : (W₁⁄F).toAffine.Point} :
    P ∈ φ.ker ↔ ∀ z ∈ φ.fieldPullback.fieldRange, translation W₁ P z = z := by
  rw [ker_def]; exact mem_translationFixingSubgroup_iff W₁

/-- **The kernel is finite**, the pulled-back field being of finite index. -/
instance finite_ker (φ : Isogeny W₁ W₂) : Finite φ.ker :=
  φ.ker_def ▸ finite_translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- **Postcomposition can only enlarge the kernel**: a function pulled back from `W₃` arrives
through `W₂`, so a translation fixing everything from `W₂` fixes it too. -/
theorem ker_le_ker_comp {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) : φ.ker ≤ (ψ.comp φ).ker := by
  rw [ker_def, ker_def]
  refine translationFixingSubgroup_antitone W₁ ?_
  rintro _ ⟨z, rfl⟩
  exact AlgHom.mem_fieldRange.2 ⟨ψ.fieldPullback z, by rw [comp_fieldPullback]; rfl⟩

/-- **The kernel order divides the separable degree**, the kernel being the subgroup of
translations fixing the pulled-back field and that field having finite degree. -/
theorem card_ker_dvd_separableDegree (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker ∣ φ.separableDegree := by
  have := φ.finiteDimensional
  rw [ker_def, separableDegree_def]
  exact card_translationFixingSubgroup_dvd_finSepDegree W₁ _

/-- **The separable degree bounds the kernel**, sharpening the bound by the degree. -/
theorem card_ker_le_separableDegree (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker ≤ φ.separableDegree :=
  Nat.le_of_dvd φ.separableDegree_pos φ.card_ker_dvd_separableDegree

/-- **The degree bounds the kernel**, the separable degree being at most the degree. The bound is
often strict, this being the rational kernel: equality needs the isogeny to be separable and its
geometric kernel to be rational. -/
theorem card_ker_le_degree (φ : Isogeny W₁ W₂) : Nat.card φ.ker ≤ φ.degree :=
  φ.card_ker_le_separableDegree.trans <| by
    rw [separableDegree_def, degree_def]; exact Field.finSepDegree_le_finrank _ _

/-- **An isogeny of separable degree one has a trivial kernel here**, the bound leaving no room.
This is the right hypothesis: a purely inseparable isogeny such as Frobenius has separable degree
one, so its kernel in this point-valued sense is trivial whatever its degree — its scheme-theoretic
kernel, which this file does not model, is not. -/
theorem ker_eq_bot_of_separableDegree_eq_one {φ : Isogeny W₁ W₂} (h : φ.separableDegree = 1) :
    φ.ker = ⊥ :=
  φ.ker.eq_bot_of_card_le (h ▸ φ.card_ker_le_separableDegree)

/-- **The kernel counts the degree exactly when it cuts out the pulled-back field.** This is a
*reduction*, not the separable-locus theorem: one inclusion holds for free, so the cardinality
statement and the reverse inclusion are two names for the same thing.

That inclusion is where separability enters, and over a base field that is not separably closed it
can fail: the kernel here consists of the rational points, while the extension is cut out by the
geometric ones. Deriving it from separability and rationality of the geometric kernel is not done
here. -/
theorem card_ker_eq_degree_iff (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker = φ.degree ↔
      translationFixedField W₁ φ.ker ≤ φ.fieldPullback.fieldRange := by
  have := φ.finiteDimensional
  rw [ker_def, degree_def]
  exact card_translationFixingSubgroup_eq_finrank_iff W₁ _

/-- **The kernel counts the degree as soon as `K(W₁)` is Galois over the pulled-back field and
every automorphism over that field is a translation.** This is the shape the point count needs:
given the Galois hypothesis, what is left of `deg φ = #ker φ` is a statement about automorphisms,
not about fields — are there automorphisms of `K(W₁)` over `φ^*K(W₂)` beyond the translations by
kernel points? -/
theorem card_ker_eq_degree_of_forall_exists_translation (φ : Isogeny W₁ W₂)
    [IsGalois φ.fieldPullback.fieldRange W₁.FunctionField]
    (h : ∀ σ ∈ φ.fieldPullback.fieldRange.fixingSubgroup,
      ∃ P : (W₁⁄F).toAffine.Point, translation W₁ P = σ) :
    Nat.card φ.ker = φ.degree := by
  have := φ.finiteDimensional
  rw [ker_def, degree_def]
  exact card_translationFixingSubgroup_eq_finrank_of_forall_exists_translation W₁ _ h

/-- **The kernel counts the degree exactly when `K(W₁)` is Galois over the pulled-back field and
every automorphism over it is a translation.** So the two hypotheses of
`card_ker_eq_degree_of_forall_exists_translation` are jointly necessary as well as sufficient: this
is what is left of `deg φ = #ker φ`. -/
theorem card_ker_eq_degree_iff_isGalois_and_forall_exists_translation (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker = φ.degree ↔
      IsGalois φ.fieldPullback.fieldRange W₁.FunctionField ∧
        ∀ σ ∈ φ.fieldPullback.fieldRange.fixingSubgroup,
          ∃ P : (W₁⁄F).toAffine.Point, translation W₁ P = σ := by
  have := φ.finiteDimensional
  rw [ker_def, degree_def]
  exact card_translationFixingSubgroup_eq_finrank_iff_isGalois_and_forall_exists_translation W₁ _

/-- **The identity isogeny has trivial kernel.** -/
@[simp]
theorem ker_id (W : WeierstrassCurve.Affine F) [W.IsElliptic] : (id W).ker = ⊥ :=
  ker_eq_bot_of_separableDegree_eq_one (separableDegree_id W)

end TauCeti.Isogeny

end
