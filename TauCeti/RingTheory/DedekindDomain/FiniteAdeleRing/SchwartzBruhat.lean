/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.CosetDecomposition
public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# Schwartz–Bruhat functions above a set of finite places

For any set `S` of finite places, `projectPlaces S` keeps the coordinates at `S` and sets all
others to zero. A function on a finite power of the finite adeles is Schwartz–Bruhat above `S`
if it is locally constant, depends only on this projection, and has compact projected support.
Its support in the whole adele space need not be compact. When the local integer rings are
compact, the indicator of the integral box above `S` is such a function, including when `S` is
infinite or empty.

`IsSchwartzBruhatAbove.exists_eq_sum_cosetIndicator` expresses such a function as a finite sum
of indicators of cosets of any open subgroup on whose cosets it is constant and which contains
the kernel of the projection. The coefficients are values at distinct representatives in its
support. Taking the subgroup to be a scaled integral box gives the box-coset expansion.

The definitions and expansion follow `New.IsSchwartzBruhat`, `New.integralBox`, and
`New.IsSchwartzBruhat.eq_sum_cosetIndicator` in [ShortProof], grh-lean
(https://github.com/lsernau/grh-lean), commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
`src/Lib/Weil/MixedModel/SchwartzBruhat.lean` (Apache 2.0). No source code is copied.
-/

public section
noncomputable section

open Function Set Topology

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {ι : Type*}

section Box

variable [Finite ι]

/-- The open additive subgroup of vectors integral at every place in `S`. -/
def integralBox (S : Set (HeightOneSpectrum R)) : OpenAddSubgroup (ι → FiniteAdeleRing R K) where
  carrier := {x | ∀ i, projectPlaces S x i ∈ integralAdeles R K}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro i
    rw [projectPlaces_add, Pi.add_apply]
    exact (integralAdeles R K).add_mem (hx i) (hy i)
  neg_mem' hx i := by
    rw [neg_eq_zero_sub, projectPlaces_sub, projectPlaces_zero, zero_sub, Pi.neg_apply]
    exact (integralAdeles R K).neg_mem (hx i)
  isOpen' := by
    simpa only [ofPred_forall, preimage, Function.comp_apply, SetLike.mem_coe] using
      isOpen_iInter_of_finite fun i ↦
        (isOpen_integralAdeles (R := R) (K := K)).preimage
          ((continuous_apply i).comp (continuous_projectPlaces S))

/-- Membership in the integral box can be read after projection. -/
theorem mem_integralBox_iff (S : Set (HeightOneSpectrum R)) (x : ι → FiniteAdeleRing R K) :
    x ∈ integralBox S ↔ ∀ i, projectPlaces S x i ∈ integralAdeles R K := (Iff.rfl)

/-- Projecting does not change membership in the integral box. -/
@[simp]
theorem projectPlaces_mem_integralBox (S : Set (HeightOneSpectrum R))
    (x : ι → FiniteAdeleRing R K) : projectPlaces S x ∈ integralBox S ↔ x ∈ integralBox S := by
  simp only [mem_integralBox_iff, projectPlaces_projectPlaces]

/-- The kernel of the projection is contained in the integral box. -/
theorem mem_integralBox_of_projectPlaces_eq_zero {S : Set (HeightOneSpectrum R)}
    {x : ι → FiniteAdeleRing R K} (hx : projectPlaces S x = 0) : x ∈ integralBox S := by
  simp [mem_integralBox_iff, hx]

/-- The box scaled by a finite idele `t`, namely the vectors `x` with `t⁻¹ x` integral
at every place in `S`. -/
def scaledIntegralBox (S : Set (HeightOneSpectrum R)) (t : (FiniteAdeleRing R K)ˣ) :
    OpenAddSubgroup (ι → FiniteAdeleRing R K) :=
  (integralBox S).comap (DistribMulAction.toAddMonoidEnd _ _ t⁻¹) (continuous_const_smul _)

/-- Membership in the scaled box is integrality after multiplication by `t⁻¹`. -/
@[simp]
theorem mem_scaledIntegralBox (S : Set (HeightOneSpectrum R)) (t : (FiniteAdeleRing R K)ˣ)
    (x : ι → FiniteAdeleRing R K) : x ∈ scaledIntegralBox S t ↔ t⁻¹ • x ∈ integralBox S :=
  (Iff.rfl)

/-- Scaling the box by one recovers the integral box. -/
@[simp]
theorem scaledIntegralBox_one (S : Set (HeightOneSpectrum R)) :
    scaledIntegralBox (K := K) (ι := ι) S 1 = integralBox S := by
  ext x
  simp

end Box

/-- A locally constant function depending only on `S`, with compact support after projection
onto `S`. This does not require compact support in the ambient finite adelic space. -/
structure IsSchwartzBruhatAbove (S : Set (HeightOneSpectrum R))
    (f : (ι → FiniteAdeleRing R K) → ℂ) : Prop where
  isLocallyConstant : IsLocallyConstant f
  project_eq : ∀ x, f (projectPlaces S x) = f x
  isCompact_image_support : IsCompact (projectPlaces S '' support f)

variable {S : Set (HeightOneSpectrum R)} {f g : (ι → FiniteAdeleRing R K) → ℂ}

/-- The projected support is the intersection of the support with the fixed points of the
projection, for any function that depends only on the selected places. -/
theorem image_support_projectPlaces_eq {f : (ι → FiniteAdeleRing R K) → ℂ}
    (hp : ∀ x, f (projectPlaces S x) = f x) :
    projectPlaces S '' support f = support f ∩ {x | projectPlaces S x = x} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by simpa only [mem_support, hp] using hy, projectPlaces_projectPlaces S y⟩
  · rintro ⟨hx, heq⟩
    exact ⟨x, hx, heq⟩

/-- Local constancy makes the projected support closed when the function depends only on `S`.
In particular, containment in a compact set suffices for compact projected support. -/
theorem isClosed_image_support_projectPlaces {f : (ι → FiniteAdeleRing R K) → ℂ}
    (hl : IsLocallyConstant f) (hp : ∀ x, f (projectPlaces S x) = f x) :
    IsClosed (projectPlaces S '' support f) := by
  rw [image_support_projectPlaces_eq hp]
  exact (⟨f, hl⟩ : LocallyConstant _ ℂ).isClopen_support.isClosed.inter
    (isClosed_eq (continuous_projectPlaces S) continuous_id)

/-- Schwartz–Bruhat above `S` means local constancy, dependence on the projection, and
containment of the projected support in a compact set. -/
theorem isSchwartzBruhatAbove_iff : IsSchwartzBruhatAbove S f ↔
    IsLocallyConstant f ∧ (∀ x, f (projectPlaces S x) = f x) ∧
      ∃ C, IsCompact C ∧ projectPlaces S '' support f ⊆ C := by
  constructor
  · intro hf
    exact ⟨hf.isLocallyConstant, hf.project_eq,
      _, hf.isCompact_image_support, Subset.rfl⟩
  · rintro ⟨hl, hp, C, hc, hC⟩
    exact ⟨hl, hp, hc.of_isClosed_subset (isClosed_image_support_projectPlaces hl hp) hC⟩

namespace IsSchwartzBruhatAbove

/-- The zero function is Schwartz–Bruhat above every set of places. -/
@[simp]
theorem zero : IsSchwartzBruhatAbove (K := K) (ι := ι) S 0 :=
  ⟨IsLocallyConstant.const _, fun _ ↦ rfl, by simp⟩

/-- Addition preserves Schwartz–Bruhat functions above `S`. -/
theorem add (hf : IsSchwartzBruhatAbove S f) (hg : IsSchwartzBruhatAbove S g) :
    IsSchwartzBruhatAbove S (f + g) := by
  have hp : ∀ x, (f + g) (projectPlaces S x) = (f + g) x := by
    intro x
    simp only [Pi.add_apply, hf.project_eq, hg.project_eq]
  have hl := hf.isLocallyConstant.add hg.isLocallyConstant
  have hs := isClosed_image_support_projectPlaces hl hp
  refine ⟨hl, hp, (hf.isCompact_image_support.union hg.isCompact_image_support).of_isClosed_subset
    hs ?_⟩
  exact (image_mono (support_add f g)).trans (by rw [image_union])

/-- Scalar multiplication preserves Schwartz–Bruhat functions above `S`. -/
theorem smul (hf : IsSchwartzBruhatAbove S f) (c : ℂ) : IsSchwartzBruhatAbove S (c • f) := by
  by_cases hc : c = 0
  · simp [hc]
  · refine ⟨hf.isLocallyConstant.comp (fun z ↦ c • z), fun x ↦ by simp [hf.project_eq], ?_⟩
    simpa only [support_const_smul_of_ne_zero c f hc] using hf.isCompact_image_support

open Classical in
/-- A Schwartz–Bruhat function above `S` has a finite expansion in cosets of any open additive
subgroup containing the kernel of the projection and fixing the function on its support.
Representatives lie in its support, are distinct modulo the subgroup, and the coefficients
are the values of the function at those representatives. -/
theorem exists_eq_sum_cosetIndicator (hf : IsSchwartzBruhatAbove S f)
    (H : OpenAddSubgroup (ι → FiniteAdeleRing R K))
    (hH : ∀ x, projectPlaces S x = 0 → x ∈ H)
    (hinv : ∀ x ∈ support f, ∀ u ∈ H, f (x + u) = f x) :
    ∃ s : Finset (ι → FiniteAdeleRing R K), (∀ y ∈ s, f y ≠ 0) ∧
      (∀ y ∈ s, ∀ z ∈ s, y - z ∈ H → y = z) ∧
      ∀ x, f x = ∑ y ∈ s, if x - y ∈ H then f y else 0 := by
  apply H.exists_eq_sum_indicator_sub_mem hinv ⟨projectPlaces S, continuous_projectPlaces S⟩
    _ hf.isCompact_image_support
  intro x
  apply hH
  simp

open Classical in
/-- The box-coset expansion: a Schwartz–Bruhat function above `S` constant on cosets of
`t B_S` is a finite sum of indicators of those cosets, with coefficients its values. -/
theorem exists_eq_sum_scaledIntegralBox [Finite ι] (hf : IsSchwartzBruhatAbove S f)
    (t : (FiniteAdeleRing R K)ˣ)
    (hinv : ∀ x ∈ support f, ∀ u ∈ scaledIntegralBox S t, f (x + u) = f x) :
    ∃ s : Finset (ι → FiniteAdeleRing R K), (∀ y ∈ s, f y ≠ 0) ∧
      (∀ y ∈ s, ∀ z ∈ s, y - z ∈ scaledIntegralBox S t → y = z) ∧
      ∀ x, f x = ∑ y ∈ s, if x - y ∈ scaledIntegralBox S t then f y else 0 := by
  apply hf.exists_eq_sum_cosetIndicator (scaledIntegralBox S t) _ hinv
  intro x hx
  rw [mem_scaledIntegralBox]
  apply mem_integralBox_of_projectPlaces_eq_zero
  simp [hx]

end IsSchwartzBruhatAbove

/-- The indicator of the integral box is Schwartz–Bruhat above `S`, provided the local integer
rings are compact. It is nonzero even when `S` is empty. -/
theorem isSchwartzBruhatAbove_integralBox [Finite ι]
    [∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)]
    (S : Set (HeightOneSpectrum R)) :
    IsSchwartzBruhatAbove S
      (((integralBox (K := K) (ι := ι) S).toAddSubgroup :
        Set (ι → FiniteAdeleRing R K)).indicator (fun _ ↦ (1 : ℂ))) := by
  classical
  let f : (ι → FiniteAdeleRing R K) → ℂ :=
    ((integralBox (K := K) (ι := ι) S).toAddSubgroup :
      Set (ι → FiniteAdeleRing R K)).indicator (fun _ ↦ 1)
  have hl : IsLocallyConstant f :=
    (LocallyConstant.charFn ℂ (integralBox S).isClopen).isLocallyConstant
  have hp (x : ι → FiniteAdeleRing R K) : f (projectPlaces S x) = f x := by
    simp only [f, indicator_apply]
    congr 1
    exact propext (projectPlaces_mem_integralBox S x)
  have heq : projectPlaces S '' support f =
      projectPlaces S '' (Set.univ.pi fun _ : ι ↦ (integralAdeles R K : Set _)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ integralBox S := by simpa [f, mem_support] using hy
      exact ⟨projectPlaces S y, fun i _ ↦ hy' i, projectPlaces_projectPlaces S y⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      have hy' : y ∈ integralBox S := by
        intro i
        rw [mem_integralAdeles]
        intro v
        by_cases hv : v ∈ S
        · simpa [hv] using (mem_integralAdeles.1 (hy i (mem_univ i))) v
        · simp [hv]
      simp [f, hy']
  refine ⟨hl, hp, ?_⟩
  rw [heq]
  exact (isCompact_univ_pi fun _ : ι ↦ isCompact_integralAdeles (R := R) (K := K)).image
    (continuous_projectPlaces S)

end IsDedekindDomain.FiniteAdeleRing

