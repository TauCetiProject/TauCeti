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
import TauCeti.Geometry.Diffeomorphism.Sphere.RotationFamily
import TauCeti.Geometry.Manifold.LocallyFlat.Concordance.Smooth
import TauCeti.KnotTheory.ConnectedSum.Position

/-!
# Smooth concordance classes of knots and the smooth concordance monoid

Two oriented smooth circle presentations `K₀, K₁ : S¹ → M` in a finite-dimensional smooth manifold
`M` are smoothly concordant (`TauCeti.SmoothEmbedding.Concordant`) when they are joined by a smooth
collared track `S¹ × ℝ → M × ℝ`. Packaging smooth concordance as a quotient of
`TauCeti.SmoothCircleEmbedding I M` gives the type
`TauCeti.SmoothCircleEmbedding.ConcordanceClass I M` of smooth concordance classes. Rotating the
circle parameter traces a source diffeotopy (`TauCeti.SmoothCircleEmbedding.concordant_rotate`), so
the quotient class depends only on the oriented curve up to smooth concordance; reversing the circle
parameter and transporting along ambient diffeomorphisms descend to equivalences on
`ConcordanceClass`.

When the ambient manifold is the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product
space `E` with `3 ≤ n`, smooth concordance classes carry a **canonical abelian monoid structure**
(`AddCommMonoid`) whose addition is the connected sum and whose zero is the class of any great
circle:

* **Zero.** By `TauCeti.SmoothCircleEmbedding.concordant_greatCircle`, all great circles
  `ι : ℂ →ₗᵢ E` define the same smooth concordance class (`toConcordanceClass_greatCircle`),
  including the unknot in `S³ ⊆ ℝ⁴` (`toConcordanceClass_unknot`).
* **Addition.** Every concordance class in `Sⁿ` (`2 ≤ n`) has a representative in connected-sum
  position for any great circle `ι` (`exists_rep_isConnectedSumPosition`). For `3 ≤ n`, the
  concordance class of `connectedSum K₁ K₂ h₁ h₂` depends neither on the positioned representatives
  nor on the great circle `ι`
  (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant_of_greatCircle`), and
  satisfies the unit, commutativity, and associativity laws
  (`toConcordanceClass_connectedSum`).
* **Symmetries and inverse candidate.** Orientation reversal, linear isometries of the ambient
  inner product space, the reverse mirror image, and (in `ℝⁿ⁺¹`) coordinate reflection all act as
  additive equivalences (`reverseAddEquiv`, `transLinearIsometryAddEquiv`,
  `reverseMirrorAddEquiv`, `mirrorAddEquiv`), with `reverseMirrorAddEquiv` factoring as reversal
  composed with mirroring (`reverseMirrorAddEquiv_eq_reverseAddEquiv_trans_mirrorAddEquiv`). Linear
  isometries of equal determinant induce the same automorphism
  (`transLinearIsometryAddEquiv_eq_of_det_eq`). For every concordance class `x`, the sum
  `x + reverseMirrorAddEquiv x` admits a smoothly slice representative
  (`exists_isSmoothlySlice_rep_add_reverseMirrorAddEquiv`). Showing that every smoothly slice knot
  is smoothly concordant to a great circle upgrades this monoid to an abelian group with
  `reverseMirrorAddEquiv` as negation.

In every sphere dimension `n`, smooth concordance implies topological concordance, so topological
sliceness (`TauCeti.IsTopologicallySlice`) and the smooth cobordism distance
(`TauCeti.cobordismDistance`) descend to smooth concordance classes.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.ConcordanceClass`: smooth concordance classes of oriented smooth
  circle embeddings into a manifold.
* `TauCeti.SmoothCircleEmbedding.toConcordanceClass`: the quotient map to smooth concordance
  classes.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverse`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseEquiv`: orientation reversal on
  concordance classes.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.transDiffeomorph`: transport of concordance
  classes along an ambient diffeomorphism.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.instAddCommMonoid`: the canonical abelian monoid
  structure on smooth concordance classes in `Sⁿ` for `3 ≤ n`.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.transLinearIsometryAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.reverseMirrorAddEquiv`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.mirrorAddEquiv`: the additive automorphisms and
  isomorphisms of the smooth concordance monoid.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.IsTopologicallySlice`,
  `TauCeti.SmoothCircleEmbedding.ConcordanceClass.cobordismDistance`: topological sliceness and
  smooth cobordism distance on smooth concordance classes.

## Main results

* `TauCeti.SmoothCircleEmbedding.concordant_rotate`: rotating the circle parameter preserves smooth
  concordance.
* `TauCeti.SmoothCircleEmbedding.toConcordanceClass_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.toConcordanceClass_unknot`,
  `TauCeti.SmoothCircleEmbedding.toConcordanceClass_connectedSum`: any great circle represents `0`
  and any positioned connected sum represents `+`.
* `TauCeti.SmoothCircleEmbedding.ConcordanceClass.transLinearIsometryAddEquiv_eq_of_det_eq`: linear
  isometries of the same determinant induce the same automorphism on concordance classes.
* `SmoothCircleEmbedding.ConcordanceClass.exists_isSmoothlySlice_rep_add_reverseMirrorAddEquiv`:
  every class plus its reverse mirror class has a smoothly slice representative.
* `TauCeti.SmoothEmbedding.Concordant.isTopologicallySlice_iff`: topological sliceness is invariant
  under smooth concordance in every sphere dimension.

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

/-! ### Rotating the circle parameter -/

namespace SmoothCircleEmbedding

private theorem contMDiff_circleExpShift (θ : ℝ) :
    ContMDiff (𝓡∂ 1) (𝓡 1) ∞ (fun t : unitInterval => Circle.exp (θ * t)) :=
  contMDiff_circleExp.comp (contMDiff_const.mul (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))

private def circleExpTotalDiffeomorph (θ : ℝ) :
    (unitInterval × Circle) ≃ₘ⟮(𝓡∂ 1).prod (𝓡 1), (𝓡∂ 1).prod (𝓡 1)⟯ unitInterval × Circle where
  toFun q := (q.1, Circle.exp (θ * q.1) * q.2)
  invFun q := (q.1, Circle.exp (-θ * q.1) * q.2)
  left_inv q := by
    refine Prod.ext rfl ?_
    dsimp only
    rw [← mul_assoc, ← Circle.exp_add, neg_mul, neg_add_cancel, Circle.exp_zero, one_mul]
  right_inv q := by
    refine Prod.ext rfl ?_
    dsimp only
    rw [← mul_assoc, ← Circle.exp_add, neg_mul, add_neg_cancel, Circle.exp_zero, one_mul]
  contMDiff_toFun :=
    contMDiff_fst.prodMk (((contMDiff_circleExpShift θ).comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun :=
    contMDiff_fst.prodMk
      (((contMDiff_circleExpShift (-θ)).comp contMDiff_fst).mul contMDiff_snd)

@[simp]
private theorem circleExpTotalDiffeomorph_snd (θ : ℝ) (q : unitInterval × Circle) :
    (circleExpTotalDiffeomorph θ q).2 = Circle.exp (θ * q.1) * q.2 :=
  rfl

/-- The smooth rotation diffeotopy `(t, z) ↦ exp(i θ t) * z` of the unit circle. -/
private def circleExpDiffeotopy (θ : ℝ) : Diffeotopy (𝓡 1) ∞ Circle where
  toDiffeomorph := circleExpTotalDiffeomorph θ
  fst_apply _ := rfl
  snd_apply_zero' z := by simp

/-- **Rotating the circle parameter of a smooth circle presentation yields a smoothly concordant
presentation.** -/
theorem concordant_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (K : SmoothCircleEmbedding I M) (a : Circle) :
    SmoothEmbedding.Concordant K (K.rotate a) := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective a
  have hfinal : (circleExpDiffeotopy θ).final = circleRotationHom (Circle.exp θ) :=
    _root_.Diffeomorph.ext fun z => by simp [circleExpDiffeotopy, Diffeotopy.final_apply]
  have hrot : K.compDiffeomorph (circleExpDiffeotopy θ).final = K.rotate (Circle.exp θ) := by
    rw [hfinal]
    exact SmoothEmbedding.ext fun z => by simp
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
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    {motive : ConcordanceClass I M → ConcordanceClass I P → Prop}
    (x : ConcordanceClass I M) (y : ConcordanceClass I P)
    (h : ∀ (K₁ : SmoothCircleEmbedding I M) (K₂ : SmoothCircleEmbedding I P),
      motive K₁.toConcordanceClass K₂.toConcordanceClass) :
    motive x y :=
  Quotient.inductionOn₂ x y h

/-- Every smooth concordance class is represented by some smooth circle presentation. -/
theorem exists_rep (x : ConcordanceClass I M) :
    ∃ K : SmoothCircleEmbedding I M, K.toConcordanceClass = x :=
  x.inductionOn fun K => ⟨K, rfl⟩

/-- Orientation reversal of smooth circle presentations, descended to smooth concordance classes. -/
def reverse (x : ConcordanceClass I M) : ConcordanceClass I M :=
  Quotient.map SmoothCircleEmbedding.reverse
    (fun K₁ K₂ h => SmoothEmbedding.Concordant.setoid_r_iff.2 <| by
      have hrev (K : SmoothCircleEmbedding I M) : K.reverse = K.compDiffeomorph circleReflection :=
        SmoothEmbedding.ext fun z => by simp
      rw [hrev K₁, hrev K₂]
      exact (SmoothEmbedding.Concordant.setoid_r_iff.1 h).compDiffeomorph circleReflection) x

/-- The reverse of the concordance class of `K` is the concordance class of `K.reverse`. -/
@[simp]
theorem reverse_toConcordanceClass (K : SmoothCircleEmbedding I M) :
    K.toConcordanceClass.reverse = K.reverse.toConcordanceClass := by
  simp [reverse, SmoothCircleEmbedding.toConcordanceClass]; rfl

/-- Reversing orientation twice returns the original concordance class. -/
@[simp]
theorem reverse_reverse (x : ConcordanceClass I M) : x.reverse.reverse = x :=
  x.inductionOn fun K => by simp

/-- Orientation reversal on concordance classes is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (I := I) (M := M)) :=
  reverse_reverse

/-- Orientation reversal as a self-equivalence of smooth concordance classes. -/
def reverseEquiv : ConcordanceClass I M ≃ ConcordanceClass I M where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

/-- Applying `reverseEquiv` computes `reverse`. -/
@[simp]
theorem reverseEquiv_apply (x : ConcordanceClass I M) : reverseEquiv x = x.reverse := by
  simp [reverseEquiv]

/-- `reverseEquiv` is its own inverse. -/
@[simp]
theorem reverseEquiv_symm : (reverseEquiv (I := I) (M := M)).symm = reverseEquiv :=
  Equiv.ext fun x => (reverseEquiv.symm_apply_eq).2 (by simp)

section TransDiffeomorph

variable {P Q : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- Transport smooth concordance classes along a smooth diffeomorphism of the ambient manifold. -/
def transDiffeomorph (e : M ≃ₘ⟮I, I⟯ P) : ConcordanceClass I M ≃ ConcordanceClass I P where
  toFun := Quotient.map (fun K => K.transDiffeomorph e)
    (fun _ _ h => SmoothEmbedding.Concordant.setoid_r_iff.2
      ((SmoothEmbedding.Concordant.setoid_r_iff.1 h).transDiffeomorph e))
  invFun := Quotient.map (fun K => K.transDiffeomorph e.symm)
    (fun _ _ h => SmoothEmbedding.Concordant.setoid_r_iff.2
      ((SmoothEmbedding.Concordant.setoid_r_iff.1 h).transDiffeomorph e.symm))
  left_inv x := x.inductionOn fun K => by
    simp only [SmoothCircleEmbedding.toConcordanceClass, Quotient.map_mk]
    congr 1
    rw [SmoothEmbedding.transDiffeomorph_transDiffeomorph, Diffeomorph.self_trans_symm,
      SmoothEmbedding.transDiffeomorph_refl]
  right_inv y := y.inductionOn fun K => by
    simp only [SmoothCircleEmbedding.toConcordanceClass, Quotient.map_mk]
    congr 1
    rw [SmoothEmbedding.transDiffeomorph_transDiffeomorph, Diffeomorph.symm_trans_self,
      SmoothEmbedding.transDiffeomorph_refl]

/-- Transporting the concordance class of `K` along `e` gives the class of
`K.transDiffeomorph e`. -/
@[simp]
theorem transDiffeomorph_toConcordanceClass (e : M ≃ₘ⟮I, I⟯ P) (K : SmoothCircleEmbedding I M) :
    transDiffeomorph e K.toConcordanceClass = toConcordanceClass (K.transDiffeomorph e) := by
  simp [ConcordanceClass, transDiffeomorph, SmoothCircleEmbedding.toConcordanceClass]; rfl

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

/-! ### The canonical abelian monoid structure in dimension `n ≥ 3` -/

/-- Every `(n + 1)`-dimensional real inner product space with `1 ≤ n` admits a linear isometric
embedding of `ℂ`, cutting out a great circle in its unit sphere `Sⁿ`. -/
theorem nonempty_linearIsometry_complex (hn : 1 ≤ n) : Nonempty (ℂ →ₗᵢ[ℝ] E) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let b := stdOrthonormalBasis ℝ E
  have hdim : finrank ℝ E = n + 1 := Fact.out
  let i₀ : Fin (finrank ℝ E) := ⟨0, by omega⟩
  let i₁ : Fin (finrank ℝ E) := ⟨1, by omega⟩
  let p : sphere (0 : E) 1 := ⟨b i₀, by simp [b.orthonormal.1]⟩
  let v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    ⟨⟨b i₁, Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (b.orthonormal.2 (by simp [i₀, i₁]))⟩,
      mem_sphere_zero_iff_norm.2 (by simp [b.orthonormal.1])⟩
  exact ⟨sphereRotationPlane p v⟩

namespace ConcordanceClass

section Monoid

variable [Fact (3 ≤ n)]

/-- The zero smooth concordance class in `Sⁿ` (`n ≥ 3`): the class of any great circle. -/
instance instZero : Zero (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  zero :=
    let ι₀ := (nonempty_linearIsometry_complex (E := E) (n := n)
      (le_trans (by decide) (Fact.out : 3 ≤ n))).some
    (greatCircle (n := n) ι₀).toConcordanceClass

/-- Addition of smooth concordance classes in `Sⁿ` (`n ≥ 3`), given by the connected sum of
positioned representatives. -/
instance instAdd : Add (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  add x y :=
    let hn2 : 2 ≤ n := le_trans (by decide) (Fact.out : 3 ≤ n)
    let ι₀ := (nonempty_linearIsometry_complex (E := E) (n := n)
      (le_trans (by decide) (Fact.out : 3 ≤ n))).some
    let hx := x.exists_rep_isConnectedSumPosition hn2 ι₀
    let hy := y.exists_rep_isConnectedSumPosition hn2 ι₀
    (connectedSum hx.choose hy.choose hx.choose_spec.1 hy.choose_spec.1).toConcordanceClass

private theorem two_le_of_fact (n : ℕ) [Fact (3 ≤ n)] : 2 ≤ n :=
  le_trans (by decide) (Fact.out : 3 ≤ n)

private def defaultGreatCircle (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)] [Fact (3 ≤ n)] : ℂ →ₗᵢ[ℝ] E :=
  (nonempty_linearIsometry_complex (E := E) (n := n)
    (le_trans (by decide) (Fact.out : 3 ≤ n))).some

private def posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose

private theorem isConnectedSumPosition_posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    IsConnectedSumPosition (defaultGreatCircle E n) (posRep x) :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose_spec.1

private theorem toConcordanceClass_posRep (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (posRep x).toConcordanceClass = x :=
  (x.exists_rep_isConnectedSumPosition (two_le_of_fact n) (defaultGreatCircle E n)).choose_spec.2

private theorem zero_eq_defaultGreatCircle :
    (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) =
      (greatCircle (n := n) (defaultGreatCircle E n)).toConcordanceClass :=
  rfl

private theorem add_eq_posRep (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x + y = (connectedSum (posRep x) (posRep y)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)).toConcordanceClass :=
  rfl

private theorem add_toConcordanceClass_eq {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    K₁.toConcordanceClass + K₂.toConcordanceClass =
      (connectedSum K₁ K₂ h₁ h₂).toConcordanceClass := by
  rw [add_eq_posRep]
  exact (concordant_connectedSum_of_concordant_of_greatCircle (Fact.out : 3 ≤ n)
    (isConnectedSumPosition_posRep _) (isConnectedSumPosition_posRep _) h₁ h₂
    (toConcordanceClass_eq_iff.1 (toConcordanceClass_posRep _))
    (toConcordanceClass_eq_iff.1 (toConcordanceClass_posRep _))).toConcordanceClass_eq

/-- **The smooth knot concordance monoid.** In a sphere `Sⁿ` of dimension `n ≥ 3`, smooth
concordance classes form an abelian monoid under the connected sum, with the class of any great
circle as zero. -/
instance instAddCommMonoid : AddCommMonoid (ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) where
  zero_add x := by
    let ι₀ := defaultGreatCircle E n
    rw [zero_eq_defaultGreatCircle]
    conv_lhs => rw [← toConcordanceClass_posRep x]
    rw [add_toConcordanceClass_eq (isConnectedSumPosition_greatCircle ι₀)
      (isConnectedSumPosition_posRep x)]
    exact (concordant_greatCircle_connectedSum ι₀
      (isConnectedSumPosition_greatCircle ι₀) (isConnectedSumPosition_posRep x))
      |>.toConcordanceClass_eq.trans (toConcordanceClass_posRep x)
  add_zero x := by
    let ι₀ := defaultGreatCircle E n
    rw [zero_eq_defaultGreatCircle]
    conv_lhs => rw [← toConcordanceClass_posRep x]
    rw [add_toConcordanceClass_eq (isConnectedSumPosition_posRep x)
      (isConnectedSumPosition_greatCircle ι₀),
      connectedSum_greatCircle, toConcordanceClass_posRep]
  add_comm x y := by
    conv_lhs => rw [← toConcordanceClass_posRep x, ← toConcordanceClass_posRep y]
    conv_rhs => rw [← toConcordanceClass_posRep y, ← toConcordanceClass_posRep x]
    rw [add_toConcordanceClass_eq (isConnectedSumPosition_posRep x)
      (isConnectedSumPosition_posRep y),
      add_toConcordanceClass_eq (isConnectedSumPosition_posRep y)
      (isConnectedSumPosition_posRep x)]
    exact (concordant_connectedSum_comm (defaultGreatCircle E n)
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)).toConcordanceClass_eq
  add_assoc x y z := by
    have hxy : SmoothEmbedding.Concordant
        (connectedSum (posRep x) (posRep y)
          (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y))
        (posRep (x + y)) :=
      toConcordanceClass_eq_iff.1 (add_eq_posRep x y ▸ (toConcordanceClass_posRep (x + y)).symm)
    have hyz : SmoothEmbedding.Concordant
        (connectedSum (posRep y) (posRep z)
          (isConnectedSumPosition_posRep y) (isConnectedSumPosition_posRep z))
        (posRep (y + z)) :=
      toConcordanceClass_eq_iff.1 (add_eq_posRep y z ▸ (toConcordanceClass_posRep (y + z)).symm)
    rw [add_eq_posRep (x + y) z, add_eq_posRep x (y + z)]
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
    (greatCircle (n := n) ι).toConcordanceClass = 0 :=
  toConcordanceClass_greatCircle_eq (ConcordanceClass.two_le_of_fact n) ι
    (ConcordanceClass.defaultGreatCircle E n)

/-- **The connected sum of positioned knots represents `+` in the smooth concordance monoid**,
independently of the chosen great circle `ι`. -/
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
      concordant_reverse_connectedSum (two_le_of_fact n)
        (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y)
    dsimp only [reverseEquiv]
    rw [add_eq_posRep, reverse_toConcordanceClass, hc.toConcordanceClass_eq,
      toConcordanceClass_connectedSum hL₁ hL₂,
      ← hc₁.toConcordanceClass_eq, ← hc₂.toConcordanceClass_eq,
      ← reverse_toConcordanceClass, ← reverse_toConcordanceClass,
      toConcordanceClass_posRep, toConcordanceClass_posRep]

/-- `reverseAddEquiv` agrees with `reverse` on elements. -/
@[simp]
theorem reverseAddEquiv_apply (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    reverseAddEquiv x = x.reverse := by
  simp [reverseAddEquiv]

/-- Applying `reverseAddEquiv` to the class of `K` gives the class of `K.reverse`. -/
theorem reverseAddEquiv_toConcordanceClass
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseAddEquiv K.toConcordanceClass = K.reverse.toConcordanceClass := by
  simp

/-- `reverseAddEquiv` is involutive: its inverse is itself. -/
@[simp]
theorem reverseAddEquiv_symm :
    (reverseAddEquiv (E := E) (n := n)).symm = reverseAddEquiv :=
  AddEquiv.ext fun _ => reverseAddEquiv.toEquiv.symm_apply_eq.2 (by simp)

/-- Reversing the zero concordance class gives zero. -/
@[simp]
theorem reverse_zero : (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).reverse = 0 := by
  rw [← reverseAddEquiv_apply, map_zero]

/-- Orientation reversal distributes over addition of smooth concordance classes. -/
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
    -- Unfold `toEquiv` so the goal is stated in terms of `transDiffeomorph`.
    change transDiffeomorph (e.unitSphereDiffeomorph ∞) (x + y) =
      transDiffeomorph (e.unitSphereDiffeomorph ∞) x +
        transDiffeomorph (e.unitSphereDiffeomorph ∞) y
    rw [add_eq_posRep, transDiffeomorph_toConcordanceClass,
      transLinearIsometryEquiv_connectedSum
        (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep y) he,
      toConcordanceClass_connectedSum, ← transDiffeomorph_toConcordanceClass,
      ← transDiffeomorph_toConcordanceClass, toConcordanceClass_posRep, toConcordanceClass_posRep]

/-- `transLinearIsometryAddEquiv e` sends the class of `K` to the class of `K` transported along
`e.unitSphereDiffeomorph ∞`. -/
@[simp]
theorem transLinearIsometryAddEquiv_toConcordanceClass (e : E ≃ₗᵢ[ℝ] E')
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    transLinearIsometryAddEquiv e K.toConcordanceClass =
      toConcordanceClass (K.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
  simp [transLinearIsometryAddEquiv]

/-- The inverse of `transLinearIsometryAddEquiv e` is `transLinearIsometryAddEquiv e.symm`. -/
@[simp]
theorem transLinearIsometryAddEquiv_symm (e : E ≃ₗᵢ[ℝ] E') :
    (transLinearIsometryAddEquiv (n := n) e).symm = transLinearIsometryAddEquiv e.symm :=
  AddEquiv.ext fun x => x.inductionOn fun _ => by simp [transLinearIsometryAddEquiv]

/-- The identity linear isometry induces the identity additive equivalence on concordance
classes. -/
@[simp]
theorem transLinearIsometryAddEquiv_refl :
    transLinearIsometryAddEquiv (n := n) (LinearIsometryEquiv.refl ℝ E) = AddEquiv.refl _ := by
  refine AddEquiv.ext fun x => x.inductionOn fun K => ?_
  have hrefl : (LinearIsometryEquiv.refl ℝ E).unitSphereDiffeomorph (n := n) (k := n) ∞ =
      _root_.Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞ :=
    _root_.Diffeomorph.ext fun z => Subtype.ext (by simp)
  rw [transLinearIsometryAddEquiv_toConcordanceClass, hrefl, SmoothEmbedding.transDiffeomorph_refl,
    AddEquiv.refl_apply]

/-- Composing linear isometry equivalences composes the induced additive equivalences on concordance
classes. -/
theorem transLinearIsometryAddEquiv_trans (e₁ : E ≃ₗᵢ[ℝ] E') (e₂ : E' ≃ₗᵢ[ℝ] E'') :
    transLinearIsometryAddEquiv (n := n) (e₁.trans e₂) =
      (transLinearIsometryAddEquiv e₁).trans (transLinearIsometryAddEquiv e₂) := by
  refine AddEquiv.ext fun x => x.inductionOn fun K => ?_
  have hcomp : (e₁.trans e₂).unitSphereDiffeomorph (n := n) (k := n) ∞ =
      (e₁.unitSphereDiffeomorph (n := n) (k := n) ∞).trans
        (e₂.unitSphereDiffeomorph (n := n) (k := n) ∞) :=
    _root_.Diffeomorph.ext fun z => Subtype.ext (by simp)
  rw [transLinearIsometryAddEquiv_toConcordanceClass, hcomp,
    ← SmoothEmbedding.transDiffeomorph_transDiffeomorph,
    AddEquiv.trans_apply, transLinearIsometryAddEquiv_toConcordanceClass,
    transLinearIsometryAddEquiv_toConcordanceClass]

/-- **Linear isometries of the same determinant induce the same automorphism** on the smooth
concordance monoid. -/
theorem transLinearIsometryAddEquiv_eq_of_det_eq {e₁ e₂ : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e₁.toLinearEquiv : ℝ) = LinearEquiv.det e₂.toLinearEquiv) :
    transLinearIsometryAddEquiv (n := n) e₁ = transLinearIsometryAddEquiv e₂ :=
  AddEquiv.ext fun x => x.inductionOn fun K => by
    rw [transLinearIsometryAddEquiv_toConcordanceClass,
      transLinearIsometryAddEquiv_toConcordanceClass]
    exact (SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph K he)
      |>.toConcordanceClass_eq

/-- **Any orientation-preserving linear isometry of `E` acts as the identity** on the smooth
concordance monoid of `Sⁿ`. -/
theorem transLinearIsometryAddEquiv_eq_refl_of_det_eq_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = 1) :
    transLinearIsometryAddEquiv (n := n) e = AddEquiv.refl _ :=
  (transLinearIsometryAddEquiv_eq_of_det_eq (e₂ := .refl ℝ E) (by simpa using he)).trans
    transLinearIsometryAddEquiv_refl

end LinearIsometry

/-- **The reverse mirror image as an involutive additive automorphism** of the smooth concordance
monoid. It sends the class of `K` to the class of `reverseMirror ι K` for any great circle `ι`. -/
def reverseMirrorAddEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : E) 1) ≃+ ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
  let hn2 : 2 ≤ n := le_trans (by decide) (Fact.out : 3 ≤ n)
  let ι₀ := (nonempty_linearIsometry_complex (E := E) (n := n)
    (le_trans (by decide) (Fact.out : 3 ≤ n))).some
  let f : ConcordanceClass (𝓡 n) (sphere (0 : E) 1) → ConcordanceClass (𝓡 n) (sphere (0 : E) 1) :=
    Quotient.map (reverseMirror ι₀) (fun _ _ h =>
      SmoothEmbedding.Concordant.setoid_r_iff.2
        (concordant_reverseMirror_of_concordant hn2 ι₀ ι₀
          (SmoothEmbedding.Concordant.setoid_r_iff.1 h)))
  { toFun := f
    invFun := f
    left_inv := fun x => x.inductionOn fun K => by
      simp [f, SmoothCircleEmbedding.toConcordanceClass]; rfl
    right_inv := fun x => x.inductionOn fun K => by
      simp [f, SmoothCircleEmbedding.toConcordanceClass]; rfl
    map_add' := fun x y => by
      have happly (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
          f K.toConcordanceClass =
            (reverseMirror (defaultGreatCircle E n) K).toConcordanceClass := by
        simp [f, ι₀, defaultGreatCircle, SmoothCircleEmbedding.toConcordanceClass]; rfl
      have hx : (posRep x).toConcordanceClass = x := toConcordanceClass_posRep x
      have hy : (posRep y).toConcordanceClass = y := toConcordanceClass_posRep y
      conv_lhs => rw [add_eq_posRep]
      conv_rhs => rw [← hx, ← hy]
      rw [happly, happly, happly,
        reverseMirror_connectedSum (isConnectedSumPosition_posRep x)
          (isConnectedSumPosition_posRep y),
        toConcordanceClass_connectedSum] }

/-- For **every** great circle `ι`, `reverseMirrorAddEquiv` sends the concordance class of `K` to
the concordance class of `reverseMirror ι K`. -/
theorem reverseMirrorAddEquiv_toConcordanceClass (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirrorAddEquiv K.toConcordanceClass = (reverseMirror ι K).toConcordanceClass := by
  have hdef : reverseMirrorAddEquiv K.toConcordanceClass =
      (reverseMirror (defaultGreatCircle E n) K).toConcordanceClass := by
    simp [ConcordanceClass, reverseMirrorAddEquiv, defaultGreatCircle,
      SmoothCircleEmbedding.toConcordanceClass]; rfl
  rw [hdef]
  exact (concordant_reverseMirror_of_concordant (two_le_of_fact n)
    (defaultGreatCircle E n) ι (.refl K)).toConcordanceClass_eq

/-- Applying `reverseMirrorAddEquiv` twice returns the original concordance class. -/
@[simp]
theorem reverseMirrorAddEquiv_apply_reverseMirrorAddEquiv
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirrorAddEquiv (reverseMirrorAddEquiv x) = x :=
  x.inductionOn fun K => by
    rw [reverseMirrorAddEquiv_toConcordanceClass (defaultGreatCircle E n),
      reverseMirrorAddEquiv_toConcordanceClass (defaultGreatCircle E n),
      reverseMirror_reverseMirror]

/-- `reverseMirrorAddEquiv` is its own inverse. -/
@[simp]
theorem reverseMirrorAddEquiv_symm :
    (reverseMirrorAddEquiv (E := E) (n := n)).symm = reverseMirrorAddEquiv :=
  AddEquiv.ext fun _ => reverseMirrorAddEquiv.toEquiv.symm_apply_eq.2 (by simp)

/-- `reverseMirrorAddEquiv` commutes with orientation reversal on concordance classes. -/
theorem reverse_reverseMirrorAddEquiv (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (reverseMirrorAddEquiv x).reverse = reverseMirrorAddEquiv x.reverse := by
  refine x.inductionOn fun K => ?_
  let ι₀ := defaultGreatCircle E n
  let σ := (ℝ ∙ ι₀ Complex.I)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n) ∞
  have h1 : (reverseMirror ι₀ K).toConcordanceClass =
      toConcordanceClass (K.reverse.transDiffeomorph σ) := by
    rw [reverseMirror_eq_turnOver, toConcordanceClass_turnOver]
  have h2 : (reverseMirror ι₀ K.reverse).toConcordanceClass =
      toConcordanceClass (K.transDiffeomorph σ) := by
    rw [reverseMirror_eq_turnOver, K.reverse_reverse, toConcordanceClass_turnOver]
  rw [reverseMirrorAddEquiv_toConcordanceClass ι₀ K, h1,
    reverse_toConcordanceClass K, reverseMirrorAddEquiv_toConcordanceClass ι₀ K.reverse, h2]
  simp

/-- **Every smooth concordance class plus its reverse mirror class admits a smoothly slice
representative.** -/
theorem exists_isSmoothlySlice_rep_add_reverseMirrorAddEquiv
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    ∃ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1),
      TauCeti.IsSmoothlySlice K ∧ K.toConcordanceClass = x + reverseMirrorAddEquiv x := by
  let ι₀ := defaultGreatCircle E n
  refine ⟨connectedSum (posRep x) (reverseMirror ι₀ (posRep x))
      (isConnectedSumPosition_posRep x) (isConnectedSumPosition_posRep x).reverseMirror,
    isSmoothlySlice_connectedSum_reverseMirror (isConnectedSumPosition_posRep x), ?_⟩
  rw [toConcordanceClass_connectedSum, ← reverseMirrorAddEquiv_toConcordanceClass ι₀,
    toConcordanceClass_posRep]

end AddEquiv

end ConcordanceClass

end Sphere

/-! ### Euclidean spheres, mirror automorphism, and the unknot in `S³` -/

section EuclideanSphere

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- `3 ≤ m + 3` as a `Fact`, for activating the smooth concordance monoid on `S^{m + 3}` (in
particular `S³` when `m = 0`). -/
theorem three_le_add_three_fact (m : ℕ) : Fact (3 ≤ m + 3) :=
  ⟨Nat.le_add_left 3 m⟩

namespace ConcordanceClass

section Mirror

variable {n : ℕ} [Fact (3 ≤ n)]

/-- **Mirroring as an involutive additive automorphism** of the smooth concordance monoid of
`Sⁿ ⊆ ℝⁿ⁺¹`. -/
def mirrorAddEquiv :
    ConcordanceClass (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃+
      ConcordanceClass (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  transLinearIsometryAddEquiv (ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection

/-- `mirrorAddEquiv` sends the concordance class of `K` to the concordance class of `K.mirror`. -/
@[simp]
theorem mirrorAddEquiv_toConcordanceClass
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    mirrorAddEquiv K.toConcordanceClass = K.mirror.toConcordanceClass := by
  rw [mirrorAddEquiv, transLinearIsometryAddEquiv_toConcordanceClass, ← K.mirror_def]

/-- `mirrorAddEquiv` is its own inverse. -/
@[simp]
theorem mirrorAddEquiv_symm : (mirrorAddEquiv (n := n)).symm = mirrorAddEquiv := by
  rw [mirrorAddEquiv, transLinearIsometryAddEquiv_symm, Submodule.reflection_symm]

/-- Applying `mirrorAddEquiv` twice returns the original concordance class. -/
@[simp]
theorem mirrorAddEquiv_apply_mirrorAddEquiv
    (x : ConcordanceClass (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    mirrorAddEquiv (mirrorAddEquiv x) = x :=
  x.inductionOn fun _ => by simp

/-- **The reverse mirror automorphism factors as orientation reversal followed by mirroring.** -/
theorem reverseMirrorAddEquiv_eq_reverseAddEquiv_trans_mirrorAddEquiv :
    reverseMirrorAddEquiv (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n) =
      reverseAddEquiv.trans mirrorAddEquiv := by
  refine AddEquiv.ext fun x => x.inductionOn fun K => ?_
  let ι₀ := defaultGreatCircle (EuclideanSpace ℝ (Fin (n + 1))) n
  rw [AddEquiv.trans_apply, reverseAddEquiv_toConcordanceClass, mirrorAddEquiv_toConcordanceClass,
    reverseMirrorAddEquiv_toConcordanceClass ι₀]
  exact (concordant_reverseMirror_reverse_mirror ι₀ K).toConcordanceClass_eq

/-- **The reverse mirror automorphism also factors as mirroring followed by orientation
reversal.** -/
theorem reverseMirrorAddEquiv_eq_mirrorAddEquiv_trans_reverseAddEquiv :
    reverseMirrorAddEquiv (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n) =
      mirrorAddEquiv.trans reverseAddEquiv :=
  reverseMirrorAddEquiv_eq_reverseAddEquiv_trans_mirrorAddEquiv.trans <|
    AddEquiv.ext fun x => x.inductionOn fun _ => by simp

end Mirror

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

/-- **Topological sliceness is invariant under smooth concordance** in every sphere dimension
`n`. -/
theorem SmoothEmbedding.Concordant.isTopologicallySlice_iff
    {K₀ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h : SmoothEmbedding.Concordant K₀ K) :
    IsTopologicallySlice K₀ ↔ IsTopologicallySlice K := by
  obtain ⟨Φ⟩ := SmoothEmbedding.concordant_iff_nonempty.1 h
  let himm := Φ.toSmoothEmbedding.isImmersion
  let L := (himm.isImmersionOfComplement_complement ((1 : Circle), (0 : ℝ))).equiv
  have : FiniteDimensional ℝ ((EuclideanSpace ℝ (Fin 1) × ℝ) × himm.complement) :=
    L.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ himm.complement :=
    Module.Finite.of_surjective (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) _)
      Prod.snd_surjective
  have hdim := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, Module.finrank_self] at hdim
  exact Φ.topologicallyConcordant.isTopologicallySlice_iff (by simp) (by omega)

namespace SmoothCircleEmbedding.ConcordanceClass

/-- **Topological sliceness of a smooth concordance class**: a class is topologically slice when
its representatives bound locally flat disks in `Dⁿ⁺¹` (`TauCeti.IsTopologicallySlice`). -/
def IsTopologicallySlice (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) : Prop :=
  Quotient.lift TauCeti.IsTopologicallySlice
    (fun _ _ h => propext (SmoothEmbedding.Concordant.setoid_r_iff.1 h).isTopologicallySlice_iff) x

/-- The smooth concordance class of `K` is topologically slice if and only if `K` is topologically
slice. -/
@[simp]
theorem isTopologicallySlice_toConcordanceClass_iff
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    K.toConcordanceClass.IsTopologicallySlice ↔ TauCeti.IsTopologicallySlice K := by
  simp [IsTopologicallySlice, SmoothCircleEmbedding.toConcordanceClass]

/-- Orientation reversal preserves topological sliceness of smooth concordance classes. -/
@[simp]
theorem isTopologicallySlice_reverse_iff (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    x.reverse.IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  x.inductionOn fun _ => by simp

/-- The zero smooth concordance class is topologically slice. -/
@[simp]
theorem isTopologicallySlice_zero [Fact (3 ≤ n)] :
    (0 : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)).IsTopologicallySlice := by
  rw [← toConcordanceClass_greatCircle (defaultGreatCircle E n),
    isTopologicallySlice_toConcordanceClass_iff]
  exact TauCeti.isTopologicallySlice_greatCircle _

/-- Every smooth concordance class plus its reverse mirror class is topologically slice. -/
theorem isTopologicallySlice_add_reverseMirrorAddEquiv [Fact (3 ≤ n)]
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (x + reverseMirrorAddEquiv x).IsTopologicallySlice := by
  obtain ⟨K, hK, hKx⟩ := exists_isSmoothlySlice_rep_add_reverseMirrorAddEquiv x
  rw [← hKx, isTopologicallySlice_toConcordanceClass_iff]
  exact hK.isTopologicallySlice

/-- Linear isometry equivalences preserve topological sliceness of smooth concordance classes. -/
@[simp]
theorem isTopologicallySlice_transLinearIsometryAddEquiv_iff [Fact (3 ≤ n)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (e : E ≃ₗᵢ[ℝ] F) (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (transLinearIsometryAddEquiv e x).IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  x.inductionOn fun K => by
    rw [transLinearIsometryAddEquiv_toConcordanceClass, isTopologicallySlice_toConcordanceClass_iff,
      isTopologicallySlice_toConcordanceClass_iff]
    exact isTopologicallySlice_congr_linearIsometryEquiv e fun z => by simp

/-- The reverse mirror automorphism preserves topological sliceness of smooth concordance
classes. -/
@[simp]
theorem isTopologicallySlice_reverseMirrorAddEquiv_iff [Fact (3 ≤ n)]
    (x : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    (reverseMirrorAddEquiv x).IsTopologicallySlice ↔ x.IsTopologicallySlice := by
  refine x.inductionOn fun K => ?_
  let ι₀ := defaultGreatCircle E n
  rw [reverseMirrorAddEquiv_toConcordanceClass ι₀ K,
    reverseMirror_eq_turnOver, toConcordanceClass_turnOver,
    isTopologicallySlice_toConcordanceClass_iff, isTopologicallySlice_toConcordanceClass_iff]
  exact (isTopologicallySlice_congr_linearIsometryEquiv (ℝ ∙ ι₀ Complex.I)ᗮ.reflection
    fun z => by simp).trans TauCeti.isTopologicallySlice_reverse_iff

attribute [local instance] finrank_euclideanSpace_fin_succ_fact in
/-- The mirror automorphism of `Sⁿ ⊆ ℝⁿ⁺¹` preserves topological sliceness of smooth concordance
classes. -/
@[simp]
theorem isTopologicallySlice_mirrorAddEquiv_iff {m : ℕ} [Fact (3 ≤ m)]
    (x : ConcordanceClass (𝓡 m) (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :
    (mirrorAddEquiv x).IsTopologicallySlice ↔ x.IsTopologicallySlice :=
  isTopologicallySlice_transLinearIsometryAddEquiv_iff _ x

/-- **Smooth cobordism distance on smooth concordance classes**: the minimum genus of a smooth
oriented cobordism in `Sⁿ × [0, 1]` between representatives (`TauCeti.cobordismDistance`). -/
def cobordismDistance (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  Quotient.lift₂ TauCeti.cobordismDistance
    (fun _ _ _ _ h₀ h₁ => cobordismDistance_congr_concordant
      (SmoothEmbedding.Concordant.setoid_r_iff.1 h₀)
      (SmoothEmbedding.Concordant.setoid_r_iff.1 h₁)) x y

/-- On representatives, `ConcordanceClass.cobordismDistance` agrees with
`TauCeti.cobordismDistance`. -/
@[simp]
theorem cobordismDistance_toConcordanceClass
    (K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance K₀.toConcordanceClass K₁.toConcordanceClass =
      TauCeti.cobordismDistance K₀ K₁ := by
  simp [cobordismDistance, SmoothCircleEmbedding.toConcordanceClass]

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

/-- Linear isometry equivalences preserve smooth cobordism distance on concordance classes. -/
@[simp]
theorem cobordismDistance_transLinearIsometryAddEquiv [Fact (3 ≤ n)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (e : E ≃ₗᵢ[ℝ] F) (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance (transLinearIsometryAddEquiv e x) (transLinearIsometryAddEquiv e y) =
      cobordismDistance x y :=
  x.inductionOn₂ y fun _ _ => by simp

attribute [local instance] finrank_euclideanSpace_fin_succ_fact in
/-- The mirror automorphism of `Sⁿ ⊆ ℝⁿ⁺¹` preserves smooth cobordism distance. -/
@[simp]
theorem cobordismDistance_mirrorAddEquiv {m : ℕ} [Fact (3 ≤ m)]
    (x y : ConcordanceClass (𝓡 m) (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :
    cobordismDistance (mirrorAddEquiv x) (mirrorAddEquiv y) = cobordismDistance x y :=
  cobordismDistance_transLinearIsometryAddEquiv _ x y

/-- The reverse mirror automorphism preserves smooth cobordism distance. -/
@[simp]
theorem cobordismDistance_reverseMirrorAddEquiv [Fact (3 ≤ n)]
    (x y : ConcordanceClass (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance (reverseMirrorAddEquiv x) (reverseMirrorAddEquiv y) =
      cobordismDistance x y := by
  refine x.inductionOn₂ y fun K₀ K₁ => ?_
  let ι₀ := defaultGreatCircle E n
  rw [reverseMirrorAddEquiv_toConcordanceClass ι₀ K₀,
    reverseMirrorAddEquiv_toConcordanceClass ι₀ K₁,
    reverseMirror_eq_turnOver, reverseMirror_eq_turnOver,
    toConcordanceClass_turnOver, toConcordanceClass_turnOver,
    cobordismDistance_toConcordanceClass, TauCeti.cobordismDistance_transDiffeomorph,
    TauCeti.cobordismDistance_reverse_left, TauCeti.cobordismDistance_reverse_right,
    cobordismDistance_toConcordanceClass]

end SmoothCircleEmbedding.ConcordanceClass

end Invariants

end TauCeti
