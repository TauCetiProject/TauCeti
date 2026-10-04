/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Tangent distributions and involutivity

A *distribution* on a manifold `M` assigns to every point `x` a linear subspace `D x` of the
tangent space `T_x M`. It is a `C^n` distribution of rank `k` when near every point it is spanned
by `k` vector fields of class `C^n` whose values are linearly independent, that is, when it admits
`C^n` local frames. It is *involutive* when the Lie bracket of two vector fields tangent to `D` is
again tangent to `D`. Involutivity is the hypothesis of the Frobenius theorem, which is not proved
here: on a real manifold modelled on a finite-dimensional space, it makes an involutive smooth
distribution the tangent field of a foliation.

The distribution is recorded as the family of subspaces `D : Π x, Submodule 𝕜 (TangentSpace I x)`,
while its regularity and involutivity are predicates on that family.

## Main definitions

* `TauCeti.IsDistributionFrameOn I n D X U`: the vector fields `X i` form a `C^n` local frame of
  `D` on `U`.
* `TauCeti.IsContMDiffDistribution I n k D`: `D` is a `C^n` distribution of rank `k`.
* `TauCeti.IsInvolutiveDistribution I D`: `D` is involutive.
* `TauCeti.standardContactDistribution 𝕜`: the kernel of `dz - x dy` on `𝕜³`.

## Main results

* `TauCeti.isDistributionFrameOn_top_iff`: local frames of the whole tangent bundle, in the sense
  of `IsLocalFrameOn`, are the local frames of the distribution `⊤`.
* `TauCeti.IsContMDiffDistribution.finrank_eq`: a distribution of rank `k` has `k`-dimensional
  fibres.
* `TauCeti.isContMDiffDistribution_top` and `TauCeti.isInvolutiveDistribution_top`: the whole
  tangent bundle is a `C^n` involutive distribution.
* `TauCeti.mlieBracket_sum_smul_mem`: if vector fields differentiable at `x` have values and
  pairwise Lie brackets at `x` in a subspace `D` of the tangent space there, then so does the Lie
  bracket of any two of their combinations with coefficients differentiable at `x`. This is the
  computation behind the frame criterion for involutivity.
* `TauCeti.isContMDiffDistribution_const` and `TauCeti.isInvolutiveDistribution_const`: a fixed
  finite-dimensional (respectively closed) subspace `S` of a normed space `E`, taken at every
  point, is a `C^n` (respectively involutive) distribution on `E`.
* `TauCeti.not_isInvolutiveDistribution_standardContactDistribution`: the standard contact
  distribution is a smooth distribution of rank two that is not involutive.

## Implementation notes

Involutivity quantifies over vector fields that are only differentiable on the open set where they
are tangent to `D`: one derivative is all the Lie bracket uses. Every `C^n` vector field with
`1 ≤ n` is among them, so an involutive distribution in this sense satisfies the usual condition on
smooth local sections.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (distributions, local frames, involutivity, and the Frobenius theorem).
* A. Candel, L. Conlon, *Foliations I*, AMS GSM 23 (2000), Chapter 1.
-/

public section

noncomputable section

open Set Filter Function Module Bundle VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n m : ℕ∞ω} {k : ℕ} {ι : Type*}

section Frame

variable (I n) in
/-- The vector fields `X i` form a `C^n` local frame of the distribution `D` on the set `U`: each
`X i` is `C^n` on `U`, and at every point `x` of `U` the values `X i x` form a basis of `D x`. -/
structure IsDistributionFrameOn (D : Π x : M, Submodule 𝕜 (TangentSpace I x))
    (X : ι → Π x : M, TangentSpace I x) (U : Set M) : Prop where
  /-- Each member of the frame is a `C^n` vector field on `U`. -/
  contMDiffOn (i : ι) : CMDiff[U] n (T% (X i))
  /-- The values of the frame at a point of `U` are linearly independent. -/
  linearIndependent {x : M} (hx : x ∈ U) : LinearIndependent 𝕜 (X · x)
  /-- The values of the frame at a point of `U` span the subspace of the distribution there. -/
  span_eq {x : M} (hx : x ∈ U) : Submodule.span 𝕜 (range (X · x)) = D x

namespace IsDistributionFrameOn

variable {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {X : ι → Π x : M, TangentSpace I x}
  {U U' : Set M}

/-- A local frame of `D` on `U` is a local frame of `D` on every subset of `U`. -/
theorem mono (hX : IsDistributionFrameOn I n D X U) (hU : U' ⊆ U) :
    IsDistributionFrameOn I n D X U' where
  contMDiffOn i := (hX.contMDiffOn i).mono hU
  linearIndependent hx := hX.linearIndependent (hU hx)
  span_eq hx := hX.span_eq (hU hx)

/-- A `C^n` local frame is a `C^m` local frame for every `m ≤ n`. -/
theorem of_le (hX : IsDistributionFrameOn I n D X U) (hmn : m ≤ n) :
    IsDistributionFrameOn I m D X U where
  contMDiffOn i := (hX.contMDiffOn i).of_le hmn
  linearIndependent := hX.linearIndependent
  span_eq := hX.span_eq

/-- Every member of a local frame of `D` on `U` is tangent to `D` on `U`. -/
theorem apply_mem (hX : IsDistributionFrameOn I n D X U) (i : ι) {x : M} (hx : x ∈ U) :
    X i x ∈ D x :=
  hX.span_eq hx ▸ Submodule.subset_span (mem_range_self i)

/-- The subspaces of a distribution with a local frame indexed by `ι` have dimension `card ι`. -/
theorem finrank_eq [Fintype ι] (hX : IsDistributionFrameOn I n D X U) {x : M} (hx : x ∈ U) :
    finrank 𝕜 (D x) = Fintype.card ι := by
  rw [← hX.span_eq hx]
  exact finrank_span_eq_card (hX.linearIndependent hx)

end IsDistributionFrameOn

/-- The local frames of the distribution `⊤` are exactly the local frames of the tangent bundle. -/
theorem isDistributionFrameOn_top_iff {X : ι → Π x : M, TangentSpace I x} {U : Set M} :
    IsDistributionFrameOn I n (fun _ ↦ ⊤) X U ↔ IsLocalFrameOn I E n X U :=
  ⟨fun hX ↦ ⟨hX.linearIndependent, fun hx ↦ (hX.span_eq hx).ge, hX.contMDiffOn⟩,
    fun hX ↦ ⟨hX.contMDiffOn, hX.linearIndependent, fun hx ↦ top_le_iff.mp (hX.generating hx)⟩⟩

end Frame

section ContMDiff

variable (I n k) in
/-- `D` is a `C^n` distribution of rank `k`: every point has an open neighbourhood on which `D` has
a `C^n` local frame of `k` vector fields. -/
def IsContMDiffDistribution (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ X : Fin k → Π y : M, TangentSpace I y, IsDistributionFrameOn I n D X U

variable {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- A distribution has rank `k` and class `C^n` as soon as every point has a neighbourhood, not
necessarily open, on which it has a `C^n` local frame of `k` vector fields. -/
theorem IsContMDiffDistribution.of_mem_nhds
    (h : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ X : Fin k → Π y : M, TangentSpace I y,
      IsDistributionFrameOn I n D X U) :
    IsContMDiffDistribution I n k D := fun x ↦ by
  obtain ⟨U, hU, X, hX⟩ := h x
  exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, X,
    hX.mono interior_subset⟩

/-- A distribution with a global `C^n` frame of `k` vector fields is a `C^n` distribution of
rank `k`. -/
theorem IsDistributionFrameOn.isContMDiffDistribution {X : Fin k → Π x : M, TangentSpace I x}
    (hX : IsDistributionFrameOn I n D X univ) : IsContMDiffDistribution I n k D := fun x ↦
  ⟨univ, isOpen_univ, mem_univ x, X, hX⟩

/-- A distribution of rank `k` has `k`-dimensional subspaces. -/
theorem IsContMDiffDistribution.finrank_eq (hD : IsContMDiffDistribution I n k D) (x : M) :
    finrank 𝕜 (D x) = k := by
  obtain ⟨U, -, hx, X, hX⟩ := hD x
  simpa using hX.finrank_eq hx

/-- A `C^n` distribution is a `C^m` distribution for every `m ≤ n`. -/
theorem IsContMDiffDistribution.of_le (hD : IsContMDiffDistribution I n k D) (hmn : m ≤ n) :
    IsContMDiffDistribution I m k D := fun x ↦ by
  obtain ⟨U, hU, hx, X, hX⟩ := hD x
  exact ⟨U, hU, hx, X, hX.of_le hmn⟩

/-- On a manifold modelled on a finite-dimensional space, the whole tangent bundle is a `C^n`
distribution whose rank is the dimension. The local frames are those of the trivializations of the
tangent bundle. -/
theorem isContMDiffDistribution_top [FiniteDimensional 𝕜 E] [IsManifold I (n + 1) M] :
    IsContMDiffDistribution I n (finrank 𝕜 E) (fun _ : M ↦ ⊤) := fun x ↦ by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  exact ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x,
    e.localFrame (Module.finBasis 𝕜 E), isDistributionFrameOn_top_iff.mpr
      (e.isLocalFrameOn_localFrame_baseSet I n (Module.finBasis 𝕜 E))⟩

/-- A finite-dimensional subspace `S` of `E`, taken at every point of `E`, is a `C^n` distribution
on `E` whose rank is the dimension of `S`. Its local frames are constant. -/
theorem isContMDiffDistribution_const (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] :
    IsContMDiffDistribution 𝓘(𝕜, E) n (finrank 𝕜 S) (fun _ : E ↦ S) := by
  let b := Module.finBasis 𝕜 S
  refine IsDistributionFrameOn.isContMDiffDistribution (X := fun i _ ↦ (b i : E))
    ⟨fun i ↦ ?_, fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact contMDiffOn_vectorSpace_iff_contDiffOn.mpr contDiffOn_const
  · exact b.linearIndependent.map' S.subtype S.ker_subtype
  · have hspan : Submodule.span 𝕜 (range fun i ↦ (b i : E)) = S := by
      have hrange : (range fun i ↦ (b i : E)) = S.subtype '' range b := range_comp S.subtype b
      rw [hrange, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    -- The tangent spaces of the model space `E` are `E` itself, by definition.
    exact hspan

end ContMDiff

section Involutive

variable (I) in
/-- `D` is involutive: whenever two vector fields are differentiable and tangent to `D` on an open
set `U`, their Lie bracket is tangent to `D` on `U`. -/
def IsInvolutiveDistribution (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) : Prop :=
  ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃V W : Π x : M, TangentSpace I x⦄,
    MDiff[U] (T% V) → MDiff[U] (T% W) → (∀ x ∈ U, V x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
      ∀ x ∈ U, mlieBracket I V W x ∈ D x

variable {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- The defining property of an involutive distribution. -/
theorem isInvolutiveDistribution_iff : IsInvolutiveDistribution I D ↔
    ∀ ⦃U : Set M⦄, IsOpen U → ∀ ⦃V W : Π x : M, TangentSpace I x⦄,
      MDiff[U] (T% V) → MDiff[U] (T% W) → (∀ x ∈ U, V x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
        ∀ x ∈ U, mlieBracket I V W x ∈ D x :=
  Iff.rfl

/-- The Lie bracket of two vector fields that are differentiable and tangent to an involutive
distribution on an open set is tangent to it there. -/
theorem IsInvolutiveDistribution.mlieBracket_mem (hD : IsInvolutiveDistribution I D) {U : Set M}
    (hU : IsOpen U) {V W : Π x : M, TangentSpace I x} (hV : MDiff[U] (T% V))
    (hW : MDiff[U] (T% W)) (hVD : ∀ x ∈ U, V x ∈ D x) (hWD : ∀ x ∈ U, W x ∈ D x) {x : M}
    (hx : x ∈ U) : mlieBracket I V W x ∈ D x :=
  hD hU hV hW hVD hWD x hx

/-- The whole tangent bundle is involutive. -/
theorem isInvolutiveDistribution_top : IsInvolutiveDistribution I (fun _ : M ↦ ⊤) :=
  fun _ _ _ _ _ _ _ _ _ _ ↦ Submodule.mem_top

/-- A closed subspace `S` of `E`, taken at every point of `E`, is an involutive distribution on
`E`: the Lie bracket of two vector fields with values in `S` has values in `S`. -/
theorem isInvolutiveDistribution_const {S : Submodule 𝕜 E} (hS : IsClosed (S : Set E)) :
    IsInvolutiveDistribution 𝓘(𝕜, E) (fun _ : E ↦ S) := by
  intro U hU V W _ _ hV hW x hx
  have hVS := fderiv_apply_mem_of_eventually_sub_mem (f := V) hS
    (eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ S.sub_mem (hV y hy) (hV x hx))
  have hWS := fderiv_apply_mem_of_eventually_sub_mem (f := W) hS
    (eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ S.sub_mem (hW y hy) (hW x hx))
  rw [mlieBracket_eq_lieBracket]
  -- `lieBracket 𝕜 V W x` is by definition `fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`.
  exact S.sub_mem (hWS _) (hVS _)

section Combination

variable {X : ι → Π x : M, TangentSpace I x} {x : M}

/-- A finite combination of vector fields differentiable at `x`, with coefficients differentiable
at `x`, is differentiable at `x`. -/
private theorem mdifferentiableAt_sum_smul {s : Finset ι} {f : ι → M → 𝕜}
    (hf : ∀ i ∈ s, MDiffAt (f i) x) (hX : ∀ i ∈ s, MDiffAt (T% (X i)) x) :
    MDiffAt (T% (∑ i ∈ s, f i • X i)) x := by
  rw [Finset.sum_fn]
  exact MDifferentiableAt.sum_section fun i hi ↦ (hf i hi).smul_section (hX i hi)

/-- Let the vector fields `X i` be differentiable at `x`, with values at `x` and pairwise Lie
brackets at `x` in a subspace `D` of the tangent space there. Then the Lie bracket at `x` of two
combinations `∑ i, f i • X i` and `∑ j, g j • X j` whose coefficients are differentiable at `x`
also lies in `D`.

This is the pointwise computation behind the classical criterion for involutivity: a distribution
whose local frames are closed under the Lie bracket is involutive. -/
theorem mlieBracket_sum_smul_mem [IsManifold I 2 M] [CompleteSpace E]
    {D : Submodule 𝕜 (TangentSpace I x)} {s : Finset ι}
    (hX : ∀ i ∈ s, MDiffAt (T% (X i)) x) (hXD : ∀ i ∈ s, X i x ∈ D)
    (hXX : ∀ i ∈ s, ∀ j ∈ s, mlieBracket I (X i) (X j) x ∈ D) {f g : ι → M → 𝕜}
    (hf : ∀ i ∈ s, MDiffAt (f i) x) (hg : ∀ i ∈ s, MDiffAt (g i) x) :
    mlieBracket I (∑ i ∈ s, f i • X i) (∑ j ∈ s, g j • X j) x ∈ D := by
  classical
  -- Expand the right-hand combination against a vector field `Y` whose brackets with the frame
  -- lie in `D`.
  have right {Y : Π x : M, TangentSpace I x} (hY : ∀ j ∈ s, mlieBracket I Y (X j) x ∈ D) :
      ∀ t ⊆ s, mlieBracket I Y (∑ j ∈ t, g j • X j) x ∈ D := by
    intro t hts
    induction t using Finset.induction_on with
    | empty => simp [mlieBracket_zero_right]
    | insert a t hat ih =>
      obtain ⟨ha, ht⟩ := Finset.insert_subset_iff.mp hts
      rw [Finset.sum_insert hat, mlieBracket_add_right ((hg a ha).smul_section (hX a ha))
        (mdifferentiableAt_sum_smul (fun i hi ↦ hg i (ht hi)) fun i hi ↦ hX i (ht hi)),
        mlieBracket_smul_right (hg a ha) (hX a ha)]
      exact D.add_mem (D.add_mem (D.smul_mem _ (hXD a ha)) (D.smul_mem _ (hY a ha))) (ih ht)
  -- Then expand the left-hand combination, reducing to brackets of frame fields with the
  -- right-hand combination.
  have left : ∀ t ⊆ s, mlieBracket I (∑ i ∈ t, f i • X i) (∑ j ∈ s, g j • X j) x ∈ D := by
    intro t hts
    induction t using Finset.induction_on with
    | empty => simp [mlieBracket_zero_left]
    | insert a t hat ih =>
      obtain ⟨ha, ht⟩ := Finset.insert_subset_iff.mp hts
      rw [Finset.sum_insert hat, mlieBracket_add_left ((hf a ha).smul_section (hX a ha))
        (mdifferentiableAt_sum_smul (fun i hi ↦ hf i (ht hi)) fun i hi ↦ hX i (ht hi)),
        mlieBracket_smul_left (hf a ha) (hX a ha)]
      exact D.add_mem (D.add_mem (D.smul_mem _ (hXD a ha))
        (D.smul_mem _ (right (hXX a ha) s subset_rfl))) (ih ht)
  exact left s subset_rfl

end Combination

end Involutive

section Contact

variable (𝕜) in
/-- The standard contact distribution on `𝕜³`: at `p = (x, y, z)` it is the kernel of the contact
form `dz - x dy`, consisting of the vectors `(a, b, c)` with `c = x b`. -/
def standardContactDistribution (p : 𝕜 × 𝕜 × 𝕜) : Submodule 𝕜 (𝕜 × 𝕜 × 𝕜) where
  carrier := {v | v.2.2 = p.1 * v.2.1}
  add_mem' {v w} hv hw := by simp_all [mul_add]
  zero_mem' := by simp
  smul_mem' c v hv := by simp_all [mul_left_comm]

@[simp]
theorem mem_standardContactDistribution {p v : 𝕜 × 𝕜 × 𝕜} :
    v ∈ standardContactDistribution 𝕜 p ↔ v.2.2 = p.1 * v.2.1 :=
  (Iff.rfl)

variable (𝕜) in
/-- The frame of the standard contact distribution: the constant vector field `(1, 0, 0)` and the
vector field `(0, 1, x)`. -/
private def contactFrame : Fin 2 → Π p : 𝕜 × 𝕜 × 𝕜, TangentSpace 𝓘(𝕜, 𝕜 × 𝕜 × 𝕜) p
  | 0 => fun _ ↦ ((1, 0, 0) : 𝕜 × 𝕜 × 𝕜)
  | 1 => fun p ↦ ((0, 1, p.1) : 𝕜 × 𝕜 × 𝕜)

private theorem contactFrame_apply (p : 𝕜 × 𝕜 × 𝕜) :
    (contactFrame 𝕜 · p) = ![((1, 0, 0) : 𝕜 × 𝕜 × 𝕜), (0, 1, p.1)] := by
  funext i
  fin_cases i <;> rfl

/-- The vector fields `(1, 0, 0)` and `(0, 1, x)` form a `C^n` frame of the standard contact
distribution on all of `𝕜³`. -/
private theorem isDistributionFrameOn_contactFrame :
    IsDistributionFrameOn 𝓘(𝕜, 𝕜 × 𝕜 × 𝕜) n (standardContactDistribution 𝕜) (contactFrame 𝕜)
      univ where
  contMDiffOn i := by
    rw [contMDiffOn_vectorSpace_iff_contDiffOn]
    fin_cases i
    · exact contDiffOn_const
    · exact (contDiff_const.prodMk (contDiff_const.prodMk contDiff_fst)).contDiffOn
  linearIndependent {p} _ := by
    have h : LinearIndependent 𝕜 ![((1, 0, 0) : 𝕜 × 𝕜 × 𝕜), (0, 1, p.1)] := by
      refine LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero,
        zero_add, Prod.mk_eq_zero] at hst
      exact ⟨hst.1, hst.2.1⟩
    rw [contactFrame_apply]
    -- The tangent spaces of the model space `𝕜³` are `𝕜³` itself, by definition.
    exact h
  span_eq {p} _ := by
    have h : Submodule.span 𝕜 {((1, 0, 0) : 𝕜 × 𝕜 × 𝕜), (0, 1, p.1)} =
        standardContactDistribution 𝕜 p := by
      refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv ↦ ?_
      · rintro _ (rfl | rfl) <;> simp
      · refine Submodule.mem_span_pair.mpr ⟨v.1, v.2.1, ?_⟩
        rw [mem_standardContactDistribution] at hv
        ext <;> simp [hv, mul_comm]
    rw [contactFrame_apply]
    exact (congrArg (Submodule.span 𝕜) (Matrix.range_cons_cons_empty _ _ _)).trans h

variable (n) in
/-- The standard contact distribution is a `C^n` distribution of rank two. -/
theorem isContMDiffDistribution_standardContactDistribution :
    IsContMDiffDistribution 𝓘(𝕜, 𝕜 × 𝕜 × 𝕜) n 2 (standardContactDistribution 𝕜) :=
  isDistributionFrameOn_contactFrame.isContMDiffDistribution

/-- The standard contact distribution is not involutive: the Lie bracket of its frame fields
`(1, 0, 0)` and `(0, 1, x)` is the vector field `(0, 0, 1)`, which is nowhere tangent to it. -/
theorem not_isInvolutiveDistribution_standardContactDistribution :
    ¬IsInvolutiveDistribution 𝓘(𝕜, 𝕜 × 𝕜 × 𝕜) (standardContactDistribution 𝕜) := by
  intro h
  have hframe := isDistributionFrameOn_contactFrame (𝕜 := 𝕜) (n := 1)
  have hmem := h isOpen_univ ((hframe.contMDiffOn 0).mdifferentiableOn one_ne_zero)
    ((hframe.contMDiffOn 1).mdifferentiableOn one_ne_zero) (fun p hp ↦ hframe.apply_mem 0 hp)
    (fun p hp ↦ hframe.apply_mem 1 hp) 0 (mem_univ 0)
  rw [mlieBracket_eq_lieBracket] at hmem
  have hW : HasFDerivAt (fun p : 𝕜 × 𝕜 × 𝕜 ↦ ((0, 1, p.1) : 𝕜 × 𝕜 × 𝕜))
      ((0 : 𝕜 × 𝕜 × 𝕜 →L[𝕜] 𝕜).prod ((0 : 𝕜 × 𝕜 × 𝕜 →L[𝕜] 𝕜).prod
        (ContinuousLinearMap.fst 𝕜 𝕜 (𝕜 × 𝕜)))) 0 :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_fst))
  have hbracket : lieBracket 𝕜 (fun _ : 𝕜 × 𝕜 × 𝕜 ↦ ((1, 0, 0) : 𝕜 × 𝕜 × 𝕜))
      (fun p ↦ ((0, 1, p.1) : 𝕜 × 𝕜 × 𝕜)) 0 = (0, 0, 1) := by
    simp [lieBracket_eq, hW.fderiv]
  -- The frame fields `contactFrame 𝕜 0` and `contactFrame 𝕜 1` are, by their defining equations,
  -- the two maps whose bracket `hbracket` computes.
  have h001 : ((0, 0, 1) : 𝕜 × 𝕜 × 𝕜) ∈ standardContactDistribution 𝕜 0 := hbracket ▸ hmem
  simp at h001

end Contact

end TauCeti
