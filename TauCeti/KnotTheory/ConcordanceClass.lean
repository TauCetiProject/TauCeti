/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Congruence
public import TauCeti.KnotTheory.Mirror
public import TauCeti.KnotTheory.Slice.Concordance
public import TauCeti.KnotTheory.Slice.ConnectedSum
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Rotation
import TauCeti.KnotTheory.ConnectedSum.Commutativity
import TauCeti.KnotTheory.ConnectedSum.Position

/-!
# Smooth concordance classes of knots and the smooth concordance monoid

Two oriented smooth circle presentations `K₀, K₁ : S¹ → M` in a finite-dimensional smooth manifold
`M` are smoothly concordant (`TauCeti.SmoothEmbedding.Concordant`) when they are joined by a smooth
collared track `S¹ × ℝ → M × ℝ`. Packaging smooth concordance as a quotient of
`TauCeti.SmoothCircleEmbedding I M` gives the type
`TauCeti.SmoothCircleEmbedding.ConcordanceClass I M` of smooth concordance classes, equipped with
eliminators `ConcordanceClass.lift` and `ConcordanceClass.lift₂`. Rotating the circle parameter
traces a source diffeotopy (`TauCeti.SmoothCircleEmbedding.concordant_rotate`), so rotating the
circle parameter (changing the basepoint) does not change the smooth concordance class
(`TauCeti.SmoothCircleEmbedding.toConcordanceClass_rotate`); reversing the circle parameter and
transporting along ambient diffeomorphisms descend to equivalences on `ConcordanceClass`.

In the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space `E`, linear isometries
of equal determinant induce the same equivalence on `ConcordanceClass` in every dimension `n`
(`transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq`). In particular, all reflections induce a
single canonical involutive mirroring operation (`ConcordanceClass.mirror`, `mirrorEquiv`), and
composing reversal with mirroring gives the canonical reverse-mirror involution
(`ConcordanceClass.reverseMirror`, `reverseMirrorEquiv`), represented by
`SmoothCircleEmbedding.reverseMirror ι K` for every great circle `ι`
(`toConcordanceClass_reverseMirror`).

When `3 ≤ n`, smooth concordance classes in `Sⁿ` carry a **canonical abelian monoid structure**
(`AddCommMonoid`) whose addition is the connected sum and whose zero is the class of any great
circle:

* **Zero.** By `TauCeti.SmoothCircleEmbedding.concordant_greatCircle`, all great circles
  `ι : ℂ →ₗᵢ E` define the same smooth concordance class (`toConcordanceClass_greatCircle`),
  including the unknot in `S³ ⊆ ℝ⁴` (`toConcordanceClass_unknot`).
* **Addition.** Every concordance class in `Sⁿ` (`2 ≤ n`) has a representative in connected-sum
  position for any great circle `ι` (`exists_rep_isConnectedSumPosition`). For `3 ≤ n`, the
  concordance class of `connectedSum K₁ K₂ h₁ h₂` depends neither on the positioned representatives
  nor on the great circle `ι`
  (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant`), and satisfies the unit,
  commutativity, and associativity laws (`toConcordanceClass_connectedSum`).
* **Symmetries and inverse candidate.** Orientation reversal, linear isometries of the ambient
  inner product space, mirroring, and the reverse mirror image all act as additive equivalences
  (`reverseAddEquiv`, `transLinearIsometryAddEquiv`, `mirrorAddEquiv`, `reverseMirrorAddEquiv`),
  with `reverseMirrorAddEquiv = reverseAddEquiv.trans mirrorAddEquiv`. For every concordance class
  `x`, the sum `x + x.reverseMirror` admits a smoothly slice representative
  (`exists_isSmoothlySlice_rep_add_reverseMirror`). Showing that every smoothly slice knot is
  smoothly concordant to a great circle upgrades this monoid to an abelian group with
  `reverseMirrorAddEquiv` as negation.

In every sphere dimension `n`, topological sliceness (`TauCeti.IsTopologicallySlice`) descends to
smooth concordance classes because smooth concordance implies topological concordance
(`TauCeti.SmoothEmbedding.Concordant.isTopologicallySlice_iff`), while the unoriented knot cobordism
distance (`TauCeti.cobordismDistance`) descends directly from its smooth concordance invariance
(`TauCeti.cobordismDistance_congr_concordant`).

## Main definitions

* `TauCeti.SmoothCircleEmbedding.ConcordanceClass`: smooth concordance classes of oriented smooth
  circle embeddings into a manifold, with `ConcordanceClass.lift` and `ConcordanceClass.lift₂`.
* `TauCeti.SmoothCircleEmbedding.toConcordanceClass`: the quotient map to smooth concordance
  classes.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverse`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseEquiv`: orientation reversal on
  concordance classes.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.transDiffeomorph`: transport of concordance
  classes along an ambient diffeomorphism.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.mirror`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.mirrorEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseMirror`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseMirrorEquiv`: canonical mirroring and
  reverse-mirroring involutions on concordance classes in `Sⁿ` for any `n`.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.instAddCommMonoid`: the canonical abelian monoid
  structure on smooth concordance classes in `Sⁿ` for `3 ≤ n`.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.transLinearIsometryAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.mirrorAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseMirrorAddEquiv`: the additive automorphisms
  and isomorphisms of the smooth concordance monoid.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.IsTopologicallySlice`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.cobordismDistance`: topological sliceness and
  unoriented cobordism distance on smooth concordance classes.

## Main results

* `TauCeti.SmoothCircleEmbedding.concordant_rotate`: rotating the circle parameter preserves smooth
  concordance.
* `ConcordanceClass.transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq`: linear isometries of
  equal determinant induce the same equivalence on concordance classes in `Sⁿ`.
* `TauCeti.SmoothCircleEmbedding.toConcordanceClass_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.toConcordanceClass_unknot`,
  `TauCeti.SmoothCircleEmbedding.toConcordanceClass_connectedSum`: any great circle represents `0`
  and any positioned connected sum represents `+`.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.exists_isSmoothlySlice_rep_add_reverseMirror`:
  every class plus its reverse mirror class has a smoothly slice representative.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory*, Elsevier
  (2005), 319–347, Section 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175, Springer
  (1997), Chapter 8.
-/

public section

noncomputable section

open Metric Module Set Topology Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-- `3 ≤ m + 3` as a `Fact`, for activating the smooth concordance monoid on `S^{m + 3}` (in
particular `S³` when `m = 0`). -/
theorem three_le_add_three_fact (m : ℕ) : Fact (3 ≤ m + 3) :=
  ⟨Nat.le_add_left 3 m⟩

/-! ### Rotating the circle parameter -/

namespace SmoothCircleEmbedding

/-- **Rotating the circle parameter of a smooth circle presentation yields a smoothly concordant
presentation.** -/
theorem concordant_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (K : SmoothCircleEmbedding I M) (a : Circle) :
    SmoothEmbedding.Concordant K (K.rotate a) := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective a
  have hrot : K.compDiffeomorph (circleExpDiffeotopy (m := ∞) θ).final =
      K.rotate (Circle.exp θ) :=
    SmoothEmbedding.ext fun z => by simp
  exact hrot ▸ .of_concordance (.ofSourceDiffeotopy le_rfl (circleExpDiffeotopy θ) K)

/-! ### Smooth concordance classes of circle presentations -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Smooth concordance classes of oriented smooth circle presentations** in a smooth manifold `M`:
the quotient of `TauCeti.SmoothCircleEmbedding I M` by smooth concordance
(`TauCeti.SmoothEmbedding.Concordant`). -/
def ConcordanceClass (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Quotient (SmoothEmbedding.Concordant.setoid (𝓡 1) I ∞ Circle M)

/-- The smooth concordance class of an oriented smooth circle presentation. -/
def toConcordanceClass (K : SmoothCircleEmbedding I M) : ConcordanceClass I M :=
  Quotient.mk (SmoothEmbedding.Concordant.setoid (𝓡 1) I ∞ Circle M) K

/-- Two smooth circle presentations represent the same concordance class if and only if they are
smoothly concordant. -/
@[simp]
theorem toConcordanceClass_eq_iff {K₁ K₂ : SmoothCircleEmbedding I M} :
    K₁.toConcordanceClass = K₂.toConcordanceClass ↔ SmoothEmbedding.Concordant K₁ K₂ := by
  simp only [toConcordanceClass, ConcordanceClass]
  exact Quotient.eq_iff_equiv.trans SmoothEmbedding.Concordant.setoid_r_iff

/-- Rotating the circle parameter does not change the smooth concordance class. -/
@[simp]
theorem toConcordanceClass_rotate (K : SmoothCircleEmbedding I M) (a : Circle) :
    (K.rotate a).toConcordanceClass = K.toConcordanceClass :=
  toConcordanceClass_eq_iff.2 (K.concordant_rotate a).symm

end Manifold

end SmoothCircleEmbedding

section ConcordantDot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {K₁ K₂ : SmoothCircleEmbedding I M}

/-- Smoothly concordant circle presentations have equal concordance classes. -/
theorem SmoothEmbedding.Concordant.toConcordanceClass_eq
    (h : SmoothEmbedding.Concordant K₁ K₂) :
    K₁.toConcordanceClass = K₂.toConcordanceClass :=
  SmoothCircleEmbedding.toConcordanceClass_eq_iff.2 h

/-- Smoothly ambient isotopic circle presentations have equal concordance classes. -/
theorem SmoothEmbedding.SmoothAmbientIsotopic.toConcordanceClass_eq
    (h : K₁.SmoothAmbientIsotopic K₂) :
    K₁.toConcordanceClass = K₂.toConcordanceClass :=
  (h.concordant le_rfl).toConcordanceClass_eq

end ConcordantDot

namespace SmoothCircleEmbedding

namespace ConcordanceClass

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Induction principle for smooth concordance classes. -/
@[elab_as_elim]
protected theorem inductionOn {motive : ConcordanceClass I M → Prop}
    (x : ConcordanceClass I M) (h : ∀ K : SmoothCircleEmbedding I M, motive K.toConcordanceClass) :
    motive x :=
  Quotient.inductionOn x h

/-- Binary induction principle for smooth concordance classes. -/
@[elab_as_elim]
protected theorem inductionOn₂
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold I' ∞ P]
    {motive : ConcordanceClass I M → ConcordanceClass I' P → Prop}
    (x : ConcordanceClass I M) (y : ConcordanceClass I' P)
    (h : ∀ (K₁ : SmoothCircleEmbedding I M) (K₂ : SmoothCircleEmbedding I' P),
      motive K₁.toConcordanceClass K₂.toConcordanceClass) :
    motive x y :=
  Quotient.inductionOn₂ x y h

/-- Universal property of `ConcordanceClass`: a function on `SmoothCircleEmbedding I M` constant on
smooth concordance classes descends to `ConcordanceClass I M`. -/
protected def lift {α : Sort*} (f : SmoothCircleEmbedding I M → α)
    (hf : ∀ K₁ K₂, SmoothEmbedding.Concordant K₁ K₂ → f K₁ = f K₂)
    (x : ConcordanceClass I M) : α :=
  Quotient.lift f (fun K₁ K₂ h => hf K₁ K₂ (SmoothEmbedding.Concordant.setoid_r_iff.1 h)) x

/-- Evaluating `ConcordanceClass.lift` on the class of `K` computes `f K`. -/
@[simp]
theorem lift_toConcordanceClass {α : Sort*} (f : SmoothCircleEmbedding I M → α)
    (hf : ∀ K₁ K₂, SmoothEmbedding.Concordant K₁ K₂ → f K₁ = f K₂)
    (K : SmoothCircleEmbedding I M) :
    ConcordanceClass.lift f hf K.toConcordanceClass = f K := by
  rfl

/-- Binary universal property of `ConcordanceClass`: a two-argument function constant on smooth
concordance classes in each variable descends to `ConcordanceClass`. -/
protected def lift₂
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold I' ∞ P]
    {α : Sort*} (f : SmoothCircleEmbedding I M → SmoothCircleEmbedding I' P → α)
    (hf : ∀ K₁ K₂ L₁ L₂, SmoothEmbedding.Concordant K₁ L₁ →
      SmoothEmbedding.Concordant K₂ L₂ → f K₁ K₂ = f L₁ L₂)
    (x : ConcordanceClass I M) (y : ConcordanceClass I' P) : α :=
  Quotient.lift₂ f (fun K₁ K₂ L₁ L₂ h₁ h₂ =>
    hf K₁ K₂ L₁ L₂ (SmoothEmbedding.Concordant.setoid_r_iff.1 h₁)
      (SmoothEmbedding.Concordant.setoid_r_iff.1 h₂)) x y

/-- Evaluating `ConcordanceClass.lift₂` on the classes of `K₁` and `K₂` computes `f K₁ K₂`. -/
@[simp]
theorem lift₂_toConcordanceClass
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold I' ∞ P]
    {α : Sort*} (f : SmoothCircleEmbedding I M → SmoothCircleEmbedding I' P → α)
    (hf : ∀ K₁ K₂ L₁ L₂, SmoothEmbedding.Concordant K₁ L₁ →
      SmoothEmbedding.Concordant K₂ L₂ → f K₁ K₂ = f L₁ L₂)
    (K₁ : SmoothCircleEmbedding I M) (K₂ : SmoothCircleEmbedding I' P) :
    ConcordanceClass.lift₂ f hf K₁.toConcordanceClass K₂.toConcordanceClass = f K₁ K₂ := by
  rfl

/-- Every smooth concordance class is represented by some smooth circle presentation. -/
theorem exists_rep (x : ConcordanceClass I M) :
    ∃ K : SmoothCircleEmbedding I M, K.toConcordanceClass = x :=
  x.inductionOn fun K => ⟨K, rfl⟩

/-- Orientation reversal of smooth circle presentations, descended to smooth concordance classes. -/
def reverse (x : ConcordanceClass I M) : ConcordanceClass I M :=
  ConcordanceClass.lift (fun K => K.reverse.toConcordanceClass)
    (fun K₁ K₂ h => by
      rw [SmoothCircleEmbedding.reverse_def, SmoothCircleEmbedding.reverse_def]
      exact (h.compDiffeomorph circleReflection).toConcordanceClass_eq) x

/-- The reverse of the concordance class of `K` is the concordance class of `K.reverse`. -/
@[simp]
theorem reverse_toConcordanceClass (K : SmoothCircleEmbedding I M) :
    K.toConcordanceClass.reverse = K.reverse.toConcordanceClass := by
  rfl

/-- Reversing orientation twice returns the original concordance class. -/
@[simp]
theorem reverse_reverse (x : ConcordanceClass I M) : x.reverse.reverse = x :=
  x.inductionOn fun K => by simp

/-- Orientation reversal on concordance classes is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (I := I) (M := M)) :=
  reverse_reverse

/-- Orientation reversal as a self-equivalence of smooth concordance classes. -/
def reverseEquiv : ConcordanceClass I M ≃ ConcordanceClass I M :=
  reverse_involutive.toPerm reverse

/-- Applying `reverseEquiv` computes `reverse`. -/
@[simp]
theorem reverseEquiv_apply (x : ConcordanceClass I M) : reverseEquiv x = x.reverse := by
  rfl

/-- `reverseEquiv` is its own inverse. -/
@[simp]
theorem reverseEquiv_symm : (reverseEquiv (I := I) (M := M)).symm = reverseEquiv :=
  reverse_involutive.toPerm_symm

section TransDiffeomorph

variable {P Q : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- Transport smooth concordance classes along a smooth diffeomorphism of the ambient manifold. -/
def transDiffeomorph (e : M ≃ₘ⟮I, I⟯ P) : ConcordanceClass I M ≃ ConcordanceClass I P where
  toFun := ConcordanceClass.lift (fun K => toConcordanceClass (K.transDiffeomorph e))
    fun _ _ h => (h.transDiffeomorph e).toConcordanceClass_eq
  invFun := ConcordanceClass.lift (fun K => toConcordanceClass (K.transDiffeomorph e.symm))
    fun _ _ h => (h.transDiffeomorph e.symm).toConcordanceClass_eq
  left_inv x := x.inductionOn fun K => by
    simp [SmoothEmbedding.transDiffeomorph_transDiffeomorph]
  right_inv y := y.inductionOn fun K => by
    simp [SmoothEmbedding.transDiffeomorph_transDiffeomorph]

/-- Transporting the concordance class of `K` along `e` gives the class of
`K.transDiffeomorph e`. -/
@[simp]
theorem transDiffeomorph_toConcordanceClass (e : M ≃ₘ⟮I, I⟯ P) (K : SmoothCircleEmbedding I M) :
    transDiffeomorph e K.toConcordanceClass = toConcordanceClass (K.transDiffeomorph e) := by
  rfl

/-- The inverse of `transDiffeomorph e` is `transDiffeomorph e.symm`. -/
@[simp]
theorem transDiffeomorph_symm (e : M ≃ₘ⟮I, I⟯ P) :
    (transDiffeomorph e).symm = transDiffeomorph e.symm :=
  Equiv.ext fun x => ((transDiffeomorph e).symm_apply_eq).2 <| x.inductionOn fun K => by
    simp [SmoothEmbedding.transDiffeomorph_transDiffeomorph]

/-- Transporting along the identity diffeomorphism is the identity equivalence. -/
@[simp]
theorem transDiffeomorph_refl :
    transDiffeomorph (_root_.Diffeomorph.refl I M ∞) = Equiv.refl _ :=
  Equiv.ext fun x => x.inductionOn fun K => by
    rw [transDiffeomorph_toConcordanceClass, Equiv.refl_apply,
      SmoothEmbedding.transDiffeomorph_refl]

/-- Transporting along a composite diffeomorphism composes the equivalences on concordance
classes. -/
theorem transDiffeomorph_trans (e₁ : M ≃ₘ⟮I, I⟯ P) (e₂ : P ≃ₘ⟮I, I⟯ Q) :
    transDiffeomorph (e₁.trans e₂) = (transDiffeomorph e₁).trans (transDiffeomorph e₂) :=
  Equiv.ext fun x => x.inductionOn fun K => by
    simp [SmoothEmbedding.transDiffeomorph_transDiffeomorph]

/-- Ambient transport commutes with orientation reversal on concordance classes. -/
@[simp]
theorem reverse_transDiffeomorph (e : M ≃ₘ⟮I, I⟯ P) (x : ConcordanceClass I M) :
    (transDiffeomorph e x).reverse = transDiffeomorph e x.reverse :=
  x.inductionOn fun K => by simp

end TransDiffeomorph

end Manifold

end ConcordanceClass

/-! ### Concordance classes in spheres -/

section Sphere

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Turning a knot over in the plane of `ι` preserves its smooth concordance class. -/
@[simp]
theorem toConcordanceClass_turnOver (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    (turnOver ι K).toConcordanceClass = K.toConcordanceClass :=
  (concordant_turnOver ι K).symm.toConcordanceClass_eq

/-- Boosting a knot along `ι` preserves its smooth concordance class. -/
@[simp]
theorem toConcordanceClass_boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    (boost ι a K).toConcordanceClass = K.toConcordanceClass :=
  (concordant_boost ι a K).symm.toConcordanceClass_eq

/-- In a sphere of dimension `n ≥ 2`, any two great circles determine the same smooth concordance
class. -/
theorem toConcordanceClass_greatCircle_eq (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    (greatCircle (n := n) ι₁).toConcordanceClass = (greatCircle (n := n) ι₂).toConcordanceClass :=
  (concordant_greatCircle hn ι₁ ι₂).toConcordanceClass_eq

/-- **Every smooth concordance class in `Sⁿ` (`n ≥ 2`) admits a representative in connected-sum
position** for any chosen great circle `ι`. -/
theorem ConcordanceClass.exists_rep_isConnectedSumPosition (hn : 2 ≤ n) (ι : ℂ →ₗᵢ[ℝ] E)
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    ∃ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1),
      IsConnectedSumPosition ι K ∧ K.toConcordanceClass = x :=
  x.inductionOn fun K =>
    let ⟨K', hc, hpos⟩ := exists_concordant_isConnectedSumPosition_of_two_le hn ι K
    ⟨K', hpos, hc.symm.toConcordanceClass_eq⟩

/-! ### Linear isometries, mirroring, and reverse-mirroring in every dimension -/

namespace ConcordanceClass

/-- **Linear isometries of equal determinant induce the same equivalence** on smooth concordance
classes in `Sⁿ`, in every dimension `n`. -/
theorem transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq {e₁ e₂ : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e₁.toLinearEquiv : ℝ) = LinearEquiv.det e₂.toLinearEquiv) :
    transDiffeomorph (e₁.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      transDiffeomorph (e₂.unitSphereDiffeomorph (n := n) (k := n) ∞) :=
  Equiv.ext fun x => x.inductionOn fun K => by
    rw [transDiffeomorph_toConcordanceClass, transDiffeomorph_toConcordanceClass]
    exact (SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph K he)
      |>.toConcordanceClass_eq

/-- **Any orientation-preserving linear isometry of `E` acts as the identity** on smooth
concordance classes in `Sⁿ`. -/
theorem transDiffeomorph_unitSphereDiffeomorph_eq_refl_of_det_eq_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = 1) :
    transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) = Equiv.refl _ := by
  rw [transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq (e₂ := .refl ℝ E) (by simpa using he),
    LinearIsometryEquiv.unitSphereDiffeomorph_refl, transDiffeomorph_refl]

private theorem exists_det_eq_neg_one_of_fact (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (finrank ℝ E = n + 1)] :
    ∃ e : E ≃ₗᵢ[ℝ] E, (LinearEquiv.det e.toLinearEquiv : ℝ) = -1 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [(Fact.out : finrank ℝ E = n + 1)]; omega)
  exact TauCeti.exists_det_eq_neg_one (F := E)

private def defaultReflection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)] : E ≃ₗᵢ[ℝ] E :=
  (exists_det_eq_neg_one_of_fact E n).choose

private theorem det_defaultReflection :
    (LinearEquiv.det (defaultReflection E n).toLinearEquiv : ℝ) = -1 :=
  (exists_det_eq_neg_one_of_fact E n).choose_spec

/-- **Canonical mirroring on smooth concordance classes** in the unit sphere `Sⁿ` of `E`:
transport along any linear isometry of `E` of determinant `-1`. -/
def mirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  transDiffeomorph ((defaultReflection E n).unitSphereDiffeomorph (n := n) (k := n) ∞) x

/-- Every linear isometry `e : E ≃ₗᵢ[ℝ] E` of determinant `-1` acts on smooth concordance classes
as `ConcordanceClass.mirror`. -/
theorem transDiffeomorph_unitSphereDiffeomorph_eq_mirror_of_det_eq_neg_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = -1)
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) x = x.mirror :=
  Equiv.congr_fun (transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq
    (he.trans det_defaultReflection.symm)) x

/-- Mirroring twice returns the original smooth concordance class. -/
@[simp]
theorem mirror_mirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.mirror.mirror = x := by
  rw [mirror, mirror, ← Equiv.trans_apply, ← transDiffeomorph_trans,
    ← LinearIsometryEquiv.unitSphereDiffeomorph_trans,
    transDiffeomorph_unitSphereDiffeomorph_eq_refl_of_det_eq_one, Equiv.refl_apply]
  rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans, Units.val_mul,
    det_defaultReflection]
  norm_num

/-- Mirroring on smooth concordance classes is an involution. -/
theorem mirror_involutive :
    Function.Involutive (mirror (E := E) (n := n)) :=
  mirror_mirror

/-- Mirroring as a self-equivalence of smooth concordance classes in `Sⁿ`. -/
def mirrorEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  mirror_involutive.toPerm mirror

/-- Applying `mirrorEquiv` computes `mirror`. -/
@[simp]
theorem mirrorEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    mirrorEquiv x = x.mirror := by
  rfl

/-- `mirrorEquiv` is its own inverse. -/
@[simp]
theorem mirrorEquiv_symm : (mirrorEquiv (E := E) (n := n)).symm = mirrorEquiv :=
  mirror_involutive.toPerm_symm

/-- Every linear isometry of determinant `-1` induces the equivalence `mirrorEquiv` on smooth
concordance classes. -/
theorem transDiffeomorph_unitSphereDiffeomorph_eq_mirrorEquiv_of_det_eq_neg_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = -1) :
    transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) = mirrorEquiv :=
  Equiv.ext (transDiffeomorph_unitSphereDiffeomorph_eq_mirror_of_det_eq_neg_one he)

/-- Reversing the mirror image of a smooth concordance class equals mirroring its reverse. -/
@[simp]
theorem reverse_mirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.mirror.reverse = x.reverse.mirror :=
  reverse_transDiffeomorph _ x

/-- **The reverse mirror image of a smooth concordance class** in `Sⁿ`: orientation reversal
followed by mirroring. -/
def reverseMirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  x.reverse.mirror

/-- `reverseMirror` is orientation reversal followed by mirroring. -/
theorem reverseMirror_def (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverseMirror = x.reverse.mirror := by
  rfl

/-- Applying `reverseMirror` twice returns the original smooth concordance class. -/
@[simp]
theorem reverseMirror_reverseMirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverseMirror.reverseMirror = x := by
  simp [reverseMirror]

/-- `reverseMirror` on smooth concordance classes is an involution. -/
theorem reverseMirror_involutive :
    Function.Involutive (reverseMirror (E := E) (n := n)) :=
  reverseMirror_reverseMirror

/-- Reverse-mirroring as a self-equivalence of smooth concordance classes in `Sⁿ`. -/
def reverseMirrorEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  reverseMirror_involutive.toPerm reverseMirror

/-- Applying `reverseMirrorEquiv` computes `reverseMirror`. -/
@[simp]
theorem reverseMirrorEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirrorEquiv x = x.reverseMirror := by
  rfl

/-- `reverseMirrorEquiv` is its own inverse. -/
@[simp]
theorem reverseMirrorEquiv_symm :
    (reverseMirrorEquiv (E := E) (n := n)).symm = reverseMirrorEquiv :=
  reverseMirror_involutive.toPerm_symm

/-- `reverseMirrorEquiv` factors as orientation reversal followed by mirroring. -/
theorem reverseMirrorEquiv_eq_reverseEquiv_trans_mirrorEquiv :
    reverseMirrorEquiv (E := E) (n := n) = reverseEquiv.trans mirrorEquiv :=
  Equiv.ext fun _ => by rfl

/-- `reverseMirrorEquiv` also factors as mirroring followed by orientation reversal. -/
theorem reverseMirrorEquiv_eq_mirrorEquiv_trans_reverseEquiv :
    reverseMirrorEquiv (E := E) (n := n) = mirrorEquiv.trans reverseEquiv :=
  Equiv.ext fun x => (reverse_mirror x).symm

/-- `reverseMirror` commutes with orientation reversal on smooth concordance classes. -/
@[simp]
theorem reverse_reverseMirror (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverseMirror.reverse = x.reverse.reverseMirror := by
  simp [reverseMirror]

end ConcordanceClass

/-- For **every** great circle `ι`, the concordance class of
`SmoothCircleEmbedding.reverseMirror ι K` is the reverse mirror class of `K`. -/
@[simp]
theorem toConcordanceClass_reverseMirror (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    (reverseMirror ι K).toConcordanceClass = K.toConcordanceClass.reverseMirror := by
  rw [ConcordanceClass.reverseMirror, ConcordanceClass.reverse_toConcordanceClass,
    ← ConcordanceClass.transDiffeomorph_unitSphereDiffeomorph_eq_mirror_of_det_eq_neg_one
      (ConcordanceClass.det_defaultReflection (E := E) (n := n)),
    ConcordanceClass.transDiffeomorph_toConcordanceClass]
  exact (concordant_reverseMirror_of_det_eq_neg_one ι
    ConcordanceClass.det_defaultReflection K).toConcordanceClass_eq

/-! ### The canonical abelian monoid structure in dimension `n ≥ 3` -/

namespace ConcordanceClass

section Monoid

variable [Fact (3 ≤ n)]

private theorem two_le_of_fact (n : ℕ) [Fact (3 ≤ n)] : 2 ≤ n :=
  le_trans (by decide) (Fact.out : 3 ≤ n)

private def defaultGreatCircle (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)] [Fact (3 ≤ n)] : ℂ →ₗᵢ[ℝ] E :=
  (TauCeti.nonempty_linearIsometry_complex (E := E) (by
    have := (Fact.out : finrank ℝ E = n + 1)
    have := (Fact.out : 3 ≤ n)
    omega)).some

private def posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose

private theorem isConnectedSumPosition_posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    IsConnectedSumPosition (defaultGreatCircle E n) (posRep x) :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose_spec.1

private theorem toConcordanceClass_posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (posRep x).toConcordanceClass = x :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose_spec.2

-- `@[instance_reducible] def` with `attribute [instance]` keeps the instance bodies unexposed under
-- `module` so they can reference the `private` helpers `defaultGreatCircle` and `posRep` directly.
/-- The zero smooth concordance class in `Sⁿ` (`n ≥ 3`): the class of any great circle. -/
@[instance_reducible]
def instZero : Zero (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  zero := (greatCircle (n := n) (defaultGreatCircle E n)).toConcordanceClass

/-- Addition of smooth concordance classes in `Sⁿ` (`n ≥ 3`), given by the connected sum of
positioned representatives. -/
@[instance_reducible]
def instAdd : Add (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  add x y :=
    (connectedSum (posRep x) (posRep y)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)).toConcordanceClass

attribute [instance] instZero instAdd

private theorem zero_def :
    (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) =
      (greatCircle (n := n) (defaultGreatCircle E n)).toConcordanceClass := by
  rfl

private theorem add_def (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x + y = (connectedSum (posRep x) (posRep y)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)).toConcordanceClass := by
  rfl

private theorem add_toConcordanceClass_eq {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    K₁.toConcordanceClass + K₂.toConcordanceClass =
      (connectedSum K₁ K₂ h₁ h₂).toConcordanceClass := by
  rw [add_def]
  exact (concordant_connectedSum_of_concordant (Fact.out : 3 ≤ n)
    (isConnectedSumPosition_posRep _) (isConnectedSumPosition_posRep _) h₁ h₂
    (toConcordanceClass_eq_iff.1 (toConcordanceClass_posRep _))
    (toConcordanceClass_eq_iff.1 (toConcordanceClass_posRep _))).toConcordanceClass_eq

/-- **The smooth knot concordance monoid.** In a sphere `Sⁿ` of dimension `n ≥ 3`, smooth
concordance classes form an abelian monoid under the connected sum, with the class of any great
circle as zero. -/
instance instAddCommMonoid : AddCommMonoid (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  zero_add x := by
    let ι₀ := defaultGreatCircle E n
    rw [zero_def]
    conv_lhs => rw [← toConcordanceClass_posRep x]
    rw [add_toConcordanceClass_eq (isConnectedSumPosition_greatCircle ι₀)
      (isConnectedSumPosition_posRep x)]
    exact (concordant_greatCircle_connectedSum ι₀
      (isConnectedSumPosition_greatCircle ι₀) (isConnectedSumPosition_posRep x))
      |>.toConcordanceClass_eq.trans (toConcordanceClass_posRep x)
  add_zero x := by
    let ι₀ := defaultGreatCircle E n
    rw [zero_def]
    conv_lhs => rw [← toConcordanceClass_posRep x]
    rw [add_toConcordanceClass_eq (isConnectedSumPosition_posRep x)
      (isConnectedSumPosition_greatCircle ι₀),
      connectedSum_greatCircle, toConcordanceClass_posRep]
  add_comm x y := by
    rw [add_def, add_def]
    exact (concordant_connectedSum_comm (defaultGreatCircle E n)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)).toConcordanceClass_eq
  add_assoc x y z := by
    have hxy : SmoothEmbedding.Concordant
        (connectedSum (posRep x) (posRep y)
          (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y))
        (posRep (x + y)) :=
      toConcordanceClass_eq_iff.1 (add_def x y ▸ (toConcordanceClass_posRep (x + y)).symm)
    have hyz : SmoothEmbedding.Concordant
        (connectedSum (posRep y) (posRep z)
          (isConnectedSumPosition_posRep y) (isConnectedSumPosition_posRep z))
        (posRep (y + z)) :=
      toConcordanceClass_eq_iff.1 (add_def y z ▸ (toConcordanceClass_posRep (y + z)).symm)
    rw [add_def (x + y) z, add_def x (y + z)]
    exact (concordant_connectedSum_assoc (Fact.out : 3 ≤ n)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)
      (isConnectedSumPosition_posRep z) (isConnectedSumPosition_posRep (x + y))
      (isConnectedSumPosition_posRep (y + z)) hxy hyz).toConcordanceClass_eq
  nsmul := nsmulRec

end Monoid

end ConcordanceClass

/-- **Every great circle represents `0` in the smooth concordance monoid.** -/
@[simp]
theorem toConcordanceClass_greatCircle [Fact (3 ≤ n)] (ι : ℂ →ₗᵢ[ℝ] E) :
    (greatCircle (n := n) ι).toConcordanceClass = 0 := by
  rw [ConcordanceClass.zero_def]
  exact toConcordanceClass_greatCircle_eq (ConcordanceClass.two_le_of_fact n) ι
    (ConcordanceClass.defaultGreatCircle E n)

/-- **The connected sum of positioned knots represents `+` in the smooth concordance monoid**,
independently of the chosen great circle `ι`. -/
@[simp]
theorem toConcordanceClass_connectedSum [Fact (3 ≤ n)] {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    (connectedSum K₁ K₂ h₁ h₂).toConcordanceClass =
      K₁.toConcordanceClass + K₂.toConcordanceClass :=
  (ConcordanceClass.add_toConcordanceClass_eq h₁ h₂).symm

/-- **A knot whose smooth concordance class is `0` is smoothly slice.** -/
theorem isSmoothlySlice_of_toConcordanceClass_eq_zero [Fact (3 ≤ n)]
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} (h : K.toConcordanceClass = 0) :
    IsSmoothlySlice K := by
  rw [← toConcordanceClass_greatCircle (ConcordanceClass.defaultGreatCircle E n)] at h
  exact (toConcordanceClass_eq_iff.1 h.symm).isSmoothlySlice

/-! ### Additive equivalences on the smooth concordance monoid -/

namespace ConcordanceClass

section AddEquiv

variable [Fact (3 ≤ n)]

/-- **Orientation reversal as an additive automorphism** of the smooth concordance monoid. -/
def reverseAddEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃+ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) where
  toEquiv := reverseEquiv
  map_add' x y := by
    obtain ⟨L₁, L₂, hL₁, hL₂, hc₁, hc₂, hc⟩ :=
      exists_concordant_reverse_connectedSum (two_le_of_fact n)
        (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)
    simp only [Equiv.toFun_as_coe, reverseEquiv_apply]
    rw [add_def, reverse_toConcordanceClass, hc.toConcordanceClass_eq,
      toConcordanceClass_connectedSum hL₁ hL₂,
      ← hc₁.toConcordanceClass_eq, ← hc₂.toConcordanceClass_eq,
      ← reverse_toConcordanceClass, ← reverse_toConcordanceClass,
      toConcordanceClass_posRep, toConcordanceClass_posRep]

/-- `reverseAddEquiv` agrees with `reverse` on elements. -/
@[simp]
theorem reverseAddEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    reverseAddEquiv x = x.reverse :=
  reverseEquiv_apply x

/-- `reverseAddEquiv` is involutive: its inverse is itself. -/
@[simp]
theorem reverseAddEquiv_symm :
    (reverseAddEquiv (E := E) (n := n)).symm = reverseAddEquiv :=
  AddEquiv.toEquiv_injective reverseEquiv_symm

/-- Reversing the zero concordance class gives zero. -/
@[simp]
theorem reverse_zero : (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).reverse = 0 := by
  rw [← reverseAddEquiv_apply, map_zero]

/-- Orientation reversal distributes over addition of smooth concordance classes. -/
@[simp]
theorem reverse_add (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (x + y).reverse = x.reverse + y.reverse := by
  rw [← reverseAddEquiv_apply, map_add, reverseAddEquiv_apply, reverseAddEquiv_apply]

section LinearIsometry

variable {E' E'' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℝ E'']
  [Fact (finrank ℝ E' = n + 1)] [Fact (finrank ℝ E'' = n + 1)]

/-- **A linear isometry equivalence of the ambient inner product spaces induces an additive
isomorphism** of smooth concordance monoids. -/
def transLinearIsometryAddEquiv (e : E ≃ₗᵢ[ℝ] E') :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃+
      ConcordanceClass (𝓡 n) (sphere (0 : E') 1) where
  toEquiv := transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)
  map_add' x y := by
    let ι₀ := defaultGreatCircle E n
    let ι' : ℂ →ₗᵢ[ℝ] E' := e.toLinearIsometry.comp ι₀
    have he : ∀ w, e (ι₀ w) = ι' w := fun _ => rfl
    simp only [Equiv.toFun_as_coe]
    rw [add_def, transDiffeomorph_toConcordanceClass,
      transDiffeomorph_connectedSum
        (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y) he,
      toConcordanceClass_connectedSum, ← transDiffeomorph_toConcordanceClass,
      ← transDiffeomorph_toConcordanceClass, toConcordanceClass_posRep, toConcordanceClass_posRep]

/-- Applying `transLinearIsometryAddEquiv e` transports along `e.unitSphereDiffeomorph ∞`. -/
theorem transLinearIsometryAddEquiv_apply (e : E ≃ₗᵢ[ℝ] E')
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    transLinearIsometryAddEquiv e x =
      transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) x := by
  rfl

/-- `transLinearIsometryAddEquiv e` sends the class of `K` to the class of `K` transported along
`e.unitSphereDiffeomorph ∞`. -/
@[simp]
theorem transLinearIsometryAddEquiv_toConcordanceClass (e : E ≃ₗᵢ[ℝ] E')
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    transLinearIsometryAddEquiv e K.toConcordanceClass =
      toConcordanceClass (K.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
  rfl

/-- `transLinearIsometryAddEquiv` commutes with orientation reversal on concordance classes. -/
@[simp]
theorem reverse_transLinearIsometryAddEquiv (e : E ≃ₗᵢ[ℝ] E')
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (transLinearIsometryAddEquiv e x).reverse = transLinearIsometryAddEquiv e x.reverse := by
  exact reverse_transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) x

/-- The inverse of `transLinearIsometryAddEquiv e` is `transLinearIsometryAddEquiv e.symm`. -/
@[simp]
theorem transLinearIsometryAddEquiv_symm (e : E ≃ₗᵢ[ℝ] E') :
    (transLinearIsometryAddEquiv (n := n) e).symm = transLinearIsometryAddEquiv e.symm :=
  AddEquiv.toEquiv_injective <|
    (transDiffeomorph_symm _).trans (congrArg transDiffeomorph (e.unitSphereDiffeomorph_symm))

/-- The identity linear isometry induces the identity additive equivalence on concordance
classes. -/
@[simp]
theorem transLinearIsometryAddEquiv_refl :
    transLinearIsometryAddEquiv (n := n) (LinearIsometryEquiv.refl ℝ E) = AddEquiv.refl _ :=
  AddEquiv.toEquiv_injective <|
    (congrArg transDiffeomorph LinearIsometryEquiv.unitSphereDiffeomorph_refl).trans
      transDiffeomorph_refl

/-- Composing linear isometry equivalences composes the induced additive equivalences on concordance
classes. -/
theorem transLinearIsometryAddEquiv_trans (e₁ : E ≃ₗᵢ[ℝ] E') (e₂ : E' ≃ₗᵢ[ℝ] E'') :
    transLinearIsometryAddEquiv (n := n) (e₁.trans e₂) =
      (transLinearIsometryAddEquiv e₁).trans (transLinearIsometryAddEquiv e₂) :=
  AddEquiv.toEquiv_injective <|
    (congrArg transDiffeomorph (LinearIsometryEquiv.unitSphereDiffeomorph_trans e₁ e₂)).trans
      (transDiffeomorph_trans _ _)

/-- **Linear isometries of the same determinant induce the same automorphism** on the smooth
concordance monoid. -/
theorem transLinearIsometryAddEquiv_eq_of_det_eq {e₁ e₂ : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e₁.toLinearEquiv : ℝ) = LinearEquiv.det e₂.toLinearEquiv) :
    transLinearIsometryAddEquiv (n := n) e₁ = transLinearIsometryAddEquiv e₂ :=
  AddEquiv.toEquiv_injective (transDiffeomorph_unitSphereDiffeomorph_eq_of_det_eq he)

/-- **Any orientation-preserving linear isometry of `E` acts as the identity** on the smooth
concordance monoid of `Sⁿ`. -/
theorem transLinearIsometryAddEquiv_eq_refl_of_det_eq_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = 1) :
    transLinearIsometryAddEquiv (n := n) e = AddEquiv.refl _ :=
  AddEquiv.toEquiv_injective (transDiffeomorph_unitSphereDiffeomorph_eq_refl_of_det_eq_one he)

end LinearIsometry

/-- **Canonical mirroring as an involutive additive automorphism** of the smooth concordance monoid
of `Sⁿ`. -/
def mirrorAddEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃+ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  transLinearIsometryAddEquiv (defaultReflection E n)

/-- `mirrorAddEquiv` agrees with `mirror` on elements. -/
@[simp]
theorem mirrorAddEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    mirrorAddEquiv x = x.mirror := by
  rfl

/-- Every linear isometry of `E` of determinant `-1` induces the additive automorphism
`mirrorAddEquiv`. -/
theorem transLinearIsometryAddEquiv_eq_mirrorAddEquiv_of_det_eq_neg_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = -1) :
    transLinearIsometryAddEquiv (n := n) e = mirrorAddEquiv :=
  transLinearIsometryAddEquiv_eq_of_det_eq (he.trans det_defaultReflection.symm)

/-- `mirrorAddEquiv` is its own inverse. -/
@[simp]
theorem mirrorAddEquiv_symm : (mirrorAddEquiv (E := E) (n := n)).symm = mirrorAddEquiv :=
  AddEquiv.ext fun _ => mirrorAddEquiv.toEquiv.symm_apply_eq.2 (by simp)

/-- Mirroring the zero smooth concordance class gives zero. -/
@[simp]
theorem mirror_zero : (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).mirror = 0 := by
  rw [← mirrorAddEquiv_apply, map_zero]

/-- Mirroring distributes over addition of smooth concordance classes. -/
@[simp]
theorem mirror_add (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (x + y).mirror = x.mirror + y.mirror := by
  rw [← mirrorAddEquiv_apply, map_add, mirrorAddEquiv_apply, mirrorAddEquiv_apply]

/-- **The reverse mirror image as an involutive additive automorphism** of the smooth concordance
monoid: orientation reversal followed by mirroring. -/
def reverseMirrorAddEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃+ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  reverseAddEquiv.trans mirrorAddEquiv

/-- `reverseMirrorAddEquiv` agrees with `reverseMirror` on elements. -/
@[simp]
theorem reverseMirrorAddEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirrorAddEquiv x = x.reverseMirror := by
  rfl

/-- **The reverse mirror automorphism factors as orientation reversal followed by mirroring.** -/
theorem reverseMirrorAddEquiv_eq_reverseAddEquiv_trans_mirrorAddEquiv :
    reverseMirrorAddEquiv (E := E) (n := n) = reverseAddEquiv.trans mirrorAddEquiv := by
  rfl

/-- **The reverse mirror automorphism also factors as mirroring followed by orientation
reversal.** -/
theorem reverseMirrorAddEquiv_eq_mirrorAddEquiv_trans_reverseAddEquiv :
    reverseMirrorAddEquiv (E := E) (n := n) = mirrorAddEquiv.trans reverseAddEquiv :=
  AddEquiv.ext fun x => (reverse_mirror x).symm

/-- For every linear isometry `e : E ≃ₗᵢ[ℝ] E` of determinant `-1`, `reverseMirrorAddEquiv` is
orientation reversal followed by `transLinearIsometryAddEquiv e`. -/
theorem reverseMirrorAddEquiv_eq_reverseAddEquiv_trans_transLinearIsometryAddEquiv_of_det_eq_neg_one
    {e : E ≃ₗᵢ[ℝ] E} (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = -1) :
    reverseMirrorAddEquiv (E := E) (n := n) =
      reverseAddEquiv.trans (transLinearIsometryAddEquiv e) :=
  congrArg reverseAddEquiv.trans
    (transLinearIsometryAddEquiv_eq_mirrorAddEquiv_of_det_eq_neg_one he).symm

/-- `reverseMirrorAddEquiv` is its own inverse. -/
@[simp]
theorem reverseMirrorAddEquiv_symm :
    (reverseMirrorAddEquiv (E := E) (n := n)).symm = reverseMirrorAddEquiv :=
  AddEquiv.ext fun _ => reverseMirrorAddEquiv.toEquiv.symm_apply_eq.2 (by simp)

/-- Reverse-mirroring the zero smooth concordance class gives zero. -/
@[simp]
theorem reverseMirror_zero : (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).reverseMirror = 0 := by
  rw [← reverseMirrorAddEquiv_apply, map_zero]

/-- Reverse-mirroring distributes over addition of smooth concordance classes. -/
@[simp]
theorem reverseMirror_add (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (x + y).reverseMirror = x.reverseMirror + y.reverseMirror := by
  rw [← reverseMirrorAddEquiv_apply, map_add, reverseMirrorAddEquiv_apply,
    reverseMirrorAddEquiv_apply]

/-- **Every smooth concordance class plus its reverse mirror class admits a smoothly slice
representative.** -/
theorem exists_isSmoothlySlice_rep_add_reverseMirror
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    ∃ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1),
      TauCeti.IsSmoothlySlice K ∧ K.toConcordanceClass = x + x.reverseMirror := by
  let ι₀ := defaultGreatCircle E n
  refine ⟨connectedSum (posRep x) (SmoothCircleEmbedding.reverseMirror ι₀ (posRep x))
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep x).reverseMirror,
    isSmoothlySlice_connectedSum_reverseMirror (isConnectedSumPosition_posRep x), ?_⟩
  simp [toConcordanceClass_posRep]

end AddEquiv

end ConcordanceClass

end Sphere

/-! ### Euclidean spheres, coordinate mirroring, and the unknot in `S³` -/

section EuclideanSphere

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

namespace ConcordanceClass

/-- On `Sⁿ ⊆ ℝⁿ⁺¹`, canonical mirroring sends the concordance class of `K` to the concordance class
of the coordinate mirror image `K.mirror`. -/
@[simp]
theorem mirror_toConcordanceClass {n : ℕ}
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    K.toConcordanceClass.mirror = K.mirror.toConcordanceClass := by
  rw [K.mirror_def, ← transDiffeomorph_toConcordanceClass,
    transDiffeomorph_unitSphereDiffeomorph_eq_mirror_of_det_eq_neg_one
      (linearEquiv_det_reflection_orthogonal_singleton (by simp))]

/-- On `Sⁿ ⊆ ℝⁿ⁺¹` (`3 ≤ n`), `mirrorAddEquiv` is induced by reflection in the last coordinate
hyperplane. -/
theorem mirrorAddEquiv_eq_transLinearIsometryAddEquiv_reflection {n : ℕ} [Fact (3 ≤ n)] :
    mirrorAddEquiv (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n) =
      transLinearIsometryAddEquiv
        (ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection :=
  (transLinearIsometryAddEquiv_eq_mirrorAddEquiv_of_det_eq_neg_one
    (linearEquiv_det_reflection_orthogonal_singleton (by simp))).symm

end ConcordanceClass

attribute [local instance] three_le_add_three_fact in
/-- **The unknot in `S³` represents `0` in the smooth knot concordance monoid.** -/
@[simp]
theorem toConcordanceClass_unknot :
    SmoothCircleEmbedding.toConcordanceClass unknot = 0 := by
  rw [unknot_eq_greatCircle, toConcordanceClass_greatCircle]

end EuclideanSphere

end SmoothCircleEmbedding

/-! ### Topological sliceness and cobordism distance on concordance classes -/

section Invariants

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

namespace SmoothCircleEmbedding.ConcordanceClass

/-- **Topological sliceness of a smooth concordance class**: a class is topologically slice when
its representatives bound locally flat disks in `Dⁿ⁺¹` (`TauCeti.IsTopologicallySlice`). -/
def IsTopologicallySlice (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) : Prop :=
  ConcordanceClass.lift TauCeti.IsTopologicallySlice
    (fun _ _ h => propext h.isTopologicallySlice_iff) x

/-- The smooth concordance class of `K` is topologically slice if and only if `K` is topologically
slice. -/
@[simp]
theorem isTopologicallySlice_toConcordanceClass_iff
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    K.toConcordanceClass.IsTopologicallySlice ↔ TauCeti.IsTopologicallySlice K := by
  rfl

/-- Orientation reversal preserves topological sliceness of smooth concordance classes. -/
@[simp]
theorem isTopologicallySlice_reverse_iff (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverse.IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  x.inductionOn fun _ => by simp

/-- Linear isometry equivalences preserve topological sliceness of smooth concordance classes in
every sphere dimension `n`. -/
@[simp]
theorem isTopologicallySlice_transDiffeomorph_unitSphereDiffeomorph_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (e : E ≃ₗᵢ[ℝ] F) (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) x).IsTopologicallySlice ↔
      x.IsTopologicallySlice :=
  x.inductionOn fun K => by
    rw [transDiffeomorph_toConcordanceClass, isTopologicallySlice_toConcordanceClass_iff,
      isTopologicallySlice_toConcordanceClass_iff]
    exact isTopologicallySlice_congr_linearIsometryEquiv e fun z => by simp

/-- Mirroring preserves topological sliceness of smooth concordance classes in every sphere
dimension `n`. -/
@[simp]
theorem isTopologicallySlice_mirror_iff
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.mirror.IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  isTopologicallySlice_transDiffeomorph_unitSphereDiffeomorph_iff _ x

/-- Reverse-mirroring preserves topological sliceness of smooth concordance classes in every sphere
dimension `n`. -/
@[simp]
theorem isTopologicallySlice_reverseMirror_iff
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverseMirror.IsTopologicallySlice ↔ x.IsTopologicallySlice := by
  simp [reverseMirror]

/-- Linear isometry additive equivalences preserve topological sliceness of smooth concordance
classes. -/
@[simp]
theorem isTopologicallySlice_transLinearIsometryAddEquiv_iff [Fact (3 ≤ n)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (e : E ≃ₗᵢ[ℝ] F) (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (transLinearIsometryAddEquiv e x).IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  isTopologicallySlice_transDiffeomorph_unitSphereDiffeomorph_iff e x

/-- The zero smooth concordance class is topologically slice. -/
@[simp]
theorem isTopologicallySlice_zero [Fact (3 ≤ n)] :
    (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).IsTopologicallySlice := by
  rw [← toConcordanceClass_greatCircle (defaultGreatCircle E n),
    isTopologicallySlice_toConcordanceClass_iff]
  exact TauCeti.isTopologicallySlice_greatCircle _

/-- Every smooth concordance class plus its reverse mirror class is topologically slice. -/
theorem isTopologicallySlice_add_reverseMirror [Fact (3 ≤ n)]
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (x + x.reverseMirror).IsTopologicallySlice := by
  obtain ⟨K, hK, hKx⟩ := exists_isSmoothlySlice_rep_add_reverseMirror x
  rw [← hKx, isTopologicallySlice_toConcordanceClass_iff]
  exact hK.isTopologicallySlice

/-- **Unoriented smooth cobordism distance on smooth concordance classes**: the minimum genus (or
`⊤` if no cobordism exists) of a smooth connected orientable knot cobordism
(`TauCeti.KnotCobordism`) in `Sⁿ × [0, 1]` between the unoriented images of representatives,
ignoring knot orientations (`TauCeti.cobordismDistance`). -/
def cobordismDistance (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  ConcordanceClass.lift₂ TauCeti.cobordismDistance
    (fun _ _ _ _ h₀ h₁ => cobordismDistance_congr_concordant h₀ h₁) x y

/-- On representatives, `ConcordanceClass.cobordismDistance` agrees with
`TauCeti.cobordismDistance`. -/
@[simp]
theorem cobordismDistance_toConcordanceClass
    (K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance K₀.toConcordanceClass K₁.toConcordanceClass =
      TauCeti.cobordismDistance K₀ K₁ := by
  rfl

/-- Every smooth concordance class is at cobordism distance `0` from itself. -/
@[simp]
theorem cobordismDistance_self (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x x = 0 :=
  x.inductionOn fun _ => by simp

/-- Smooth cobordism distance on concordance classes is symmetric. -/
theorem cobordismDistance_comm (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x y = cobordismDistance y x :=
  x.inductionOn₂ y fun K₀ K₁ => by simpa using TauCeti.cobordismDistance_comm K₀ K₁

/-- Smooth cobordism distance does not depend on the orientation of the first class. -/
@[simp]
theorem cobordismDistance_reverse_left (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x.reverse y = cobordismDistance x y :=
  x.inductionOn₂ y fun _ _ => by simp

/-- Smooth cobordism distance does not depend on the orientation of the second class. -/
@[simp]
theorem cobordismDistance_reverse_right (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x y.reverse = cobordismDistance x y :=
  x.inductionOn₂ y fun _ _ => by simp

/-- Smooth cobordism distance on concordance classes is invariant under ambient diffeomorphisms of
spheres. -/
@[simp]
theorem cobordismDistance_transDiffeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1)
    (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance (transDiffeomorph Ψ x) (transDiffeomorph Ψ y) = cobordismDistance x y :=
  x.inductionOn₂ y fun _ _ => by simp

/-- Mirroring preserves smooth cobordism distance in every sphere dimension `n`. -/
@[simp]
theorem cobordismDistance_mirror
    (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x.mirror y.mirror = cobordismDistance x y :=
  cobordismDistance_transDiffeomorph _ x y

/-- Reverse-mirroring preserves smooth cobordism distance in every sphere dimension `n`. -/
@[simp]
theorem cobordismDistance_reverseMirror
    (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance x.reverseMirror y.reverseMirror = cobordismDistance x y := by
  simp [reverseMirror]

/-- Linear isometry additive equivalences preserve smooth cobordism distance on concordance
classes. -/
@[simp]
theorem cobordismDistance_transLinearIsometryAddEquiv [Fact (3 ≤ n)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (e : E ≃ₗᵢ[ℝ] F) (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance (transLinearIsometryAddEquiv e x) (transLinearIsometryAddEquiv e y) =
      cobordismDistance x y := by
  exact cobordismDistance_transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) x y

end SmoothCircleEmbedding.ConcordanceClass

end Invariants

end TauCeti
