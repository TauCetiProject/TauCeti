/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Opposite
public import TauCeti.Algebra.Homology.Kronecker
import TauCeti.Algebra.Category.ModuleCat.Injective.Semisimple
import TauCeti.LinearAlgebra.Finsupp.LSum

/-!
# The mod-two Morse cochain complex and duality for the opposite function

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n` and `X` a
Morse–Smale pseudo-gradient adapted to `f`. The **mod-two Morse cochain complex**
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseCochainComplex`) is the cochain complex
`Hom(CM_*(f), 𝔽₂)` of linear forms on the mod-two Morse chains, with differential `δa = a ∘ ∂`,
Mathlib's `ChainComplex.linearYonedaObj` of the Morse chain complex. Its cohomology is the mod-two
Morse cohomology of `(f, X)`. Since `𝔽₂` is a field, the Kronecker pairing identifies it with the
dual of the mod-two Morse homology (`IsMorseSmale.morseCohomologyEquiv`), so the two have the same
dimension in each degree.

The opposite function `-f`, with the pseudo-gradient `-X`, has the same critical points, with
Morse indices `n - ind_f`, and the trajectories of `-X` are those of `X` run backwards
(`TauCeti.Geometry.Manifold.Morse.Boundary.Opposite`). Reading a cochain of `f` in degree `i` as
the chain of `-f` with the same values on the critical points
(`IsMorseSmale.morseCochainToNegChain`) identifies the cochain module of `f` in degree `i` with the
chain module of `-f` in degree `k` whenever `i + k = n`
(`IsMorseSmale.bijective_morseCochainToNegChain`, built on the index reversal
`TauCeti.IsMorse.morseIndexNegEquiv`), and this identification carries the Morse
coboundary of `f` to the Morse boundary of `-f`
(`IsMorseSmale.morseCochainToNegChain_d_comp`). Hence the Morse cohomology of `f` in degree `i` is
isomorphic to the Morse homology of `-f` in degree `n - i`
(`IsMorseSmale.morseCohomologyEquivNegHomology`): the Morse complex of `-f` is the dual of the
Morse complex of `f`, reindexed by `k ↦ n - k`. Combined with the Kronecker pairing, the mod-two
Morse homology of `-f` in degree `k` has the dimension of that of `f` in degree `n - k`
(`IsMorseSmale.finrank_homology_morseComplex_neg`). This comparison of `-f` with `f` needs no
orientation of `M`; with integral coefficients it also involves the orientations of the unstable
manifolds. It gives mod-two Poincaré duality once Morse homology is known to be independent of the
Morse–Smale pair, which is not proved here.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseCochainComplex`: the mod-two Morse cochain complex.
* `morseCohomologyEquiv`: the Kronecker pairing identifies the Morse cohomology in degree `i` with
  the dual of the Morse homology in degree `i` (`morseCohomologyEquiv_apply`).
* `finrank_homology_morseCochainComplex`: the Morse cohomology and homology have the same
  dimension in each degree.
* `morseCochainToNegChain`: a cochain of `f` read as a chain of `-f`.
* `bijective_morseCochainToNegChain`: in complementary degrees it is an isomorphism.
* `morseCochainToNegChain_d_comp`, `morseCochainComplex_d_comp_ofHom`: it carries the Morse
  coboundary of `f` to the Morse boundary of `-f`.
* `morseCohomologyEquivNegHomology`: the Morse cohomology of `f` in degree `i` is the Morse homology
  of `-f` in degree `k`, for `i + k = n`; `morseCohomologyEquivNegHomology_homologyπ` computes it
  on the class of a cocycle.
* `finrank_homology_morseComplex_neg`: the mod-two Morse homology of `-f` in degree `k` has the
  dimension of that of `f` in degree `n - k`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual complex,
  and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and Poincaré duality).
-/

public section

universe u

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-! ### The Morse cochain complex -/

/-- **The mod-two Morse cochain complex.** The cochain complex of `ZMod 2`-vector spaces whose term
in degree `i` is the space of linear forms on the mod-two Morse chains of index `i`, with
differential `δa = a ∘ ∂` given by precomposition with the Morse boundary. Its cohomology is the
mod-two Morse cohomology of `f` and the pseudo-gradient. The coefficients `ULift (ZMod 2)` are
`ZMod 2` lifted to the universe of `M`, in which the Morse chains live. -/
-- The body is exposed so that the terms of the complex compute to spaces of linear forms on the
-- Morse chains, which the statements of `morseCochainComplex_X` and `morseCochainComplex_d_apply`
-- need.
@[expose]
noncomputable def morseCochainComplex : CochainComplex (ModuleCat (ZMod 2)) ℕ :=
  (h.morseComplex hf).linearYonedaObj (ZMod 2) (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))

/-- The term of the Morse cochain complex in degree `i` is the space of linear forms on the Morse
chains of index `i`. -/
@[simp]
theorem morseCochainComplex_X (i : ℕ) :
    (h.morseCochainComplex hf).X i = ModuleCat.of (ZMod 2)
      ((h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) :=
  (rfl)

/-- The Morse coboundary of a cochain `a` of index `i` is `a ∘ ∂`, its composite with the Morse
boundary from index `i + 1`. -/
@[simp]
theorem morseCochainComplex_d_apply (i : ℕ)
    (a : (h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) :
    (h.morseCochainComplex hf).d i (i + 1) a = (h.morseComplex hf).d (i + 1) i ≫ a :=
  (rfl)

/-- **Morse cohomology is dual to Morse homology.** The Kronecker pairing identifies the mod-two
Morse cohomology in degree `i` with the space of linear forms on the mod-two Morse homology in
degree `i`. -/
noncomputable def morseCohomologyEquiv (i : ℕ) :
    (h.morseCochainComplex hf).homology i ≃ₗ[ZMod 2]
      ((h.morseComplex hf).homology i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) :=
  ChainComplex.kroneckerEquiv (ZMod 2) (h.morseComplex hf)
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) i

/-- The identification of Morse cohomology with the dual of Morse homology is the Kronecker
pairing. -/
@[simp]
theorem morseCohomologyEquiv_apply (i : ℕ) (x : (h.morseCochainComplex hf).homology i) :
    h.morseCohomologyEquiv hf i x =
      ChainComplex.kronecker (ZMod 2) (h.morseComplex hf)
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) i x :=
  ChainComplex.kroneckerEquiv_apply _ x

/-- The mod-two Morse cohomology is finite-dimensional. -/
instance finite_homology_morseCochainComplex (i : ℕ) :
    Module.Finite (ZMod 2) ((h.morseCochainComplex hf).homology i) :=
  Module.Finite.equiv ((h.morseCohomologyEquiv hf i).trans ModuleCat.homLinearEquiv).symm

/-- **The mod-two Morse cohomology and homology have the same dimension** in each degree. -/
theorem finrank_homology_morseCochainComplex (i : ℕ) :
    finrank (ZMod 2) ((h.morseCochainComplex hf).homology i) =
      finrank (ZMod 2) ((h.morseComplex hf).homology i) := by
  rw [((h.morseCohomologyEquiv hf i).trans (ModuleCat.homLinearEquiv.trans
    (LinearEquiv.congrRight ULift.moduleEquiv))).finrank_eq]
  exact Subspace.dual_finrank_eq

/-! ### Cochains of `f` as chains of `-f` -/

/-- **A cochain of `f` read as a chain of `-f`.** The coefficient at a critical point `q` of index
`k` for `-f` of the chain associated with a cochain `a` of `f` of index `i` is the value of `a` on
`q` when `q` has index `i` for `f`, and `0` otherwise. When `i + k = n` every critical point of
index `k` for `-f` has index `i` for `f`, and this is an isomorphism
(`IsMorseSmale.bijective_morseCochainToNegChain`); otherwise it is zero
(`IsMorseSmale.morseCochainToNegChain_eq_zero`). -/
noncomputable def morseCochainToNegChain (i k : ℕ) :
    ((h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k} →₀ ZMod 2) :=
  haveI := hf.neg.finite_criticalPoints.to_subtype
  { toFun a := Finsupp.equivFunOnFinite.symm fun q ↦
      if hq : manifoldMorseIndex 𝓘(ℝ, E) f q.1 = i then
        (a (Finsupp.single ⟨⟨q.1.1, by simpa using q.1.2⟩, hq⟩ 1)).down
      else 0
    map_add' a b := by
      ext q
      by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q.1 = i
      -- The sum of two morphisms of modules acts as the sum of the underlying functions.
      · simp [hq]; rfl
      · simp [hq]
    map_smul' c a := by
      ext q
      by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q.1 = i
      -- A scalar multiple of a morphism of modules acts as the multiple of the function.
      · simp [hq]; rfl
      · simp [hq] }

/-- The coefficient at `q` of the chain of `-f` associated with a cochain `a` of `f` of index `i`
is the value of `a` on `q` if `q` has index `i` for `f`, and `0` otherwise. -/
@[simp]
theorem morseCochainToNegChain_apply {i k : ℕ}
    (a : (h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
    (q : {q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k}) :
    h.morseCochainToNegChain hf i k a q =
      if hq : manifoldMorseIndex 𝓘(ℝ, E) f q.1 = i then
        (a (Finsupp.single ⟨⟨q.1.1, by simpa using q.1.2⟩, hq⟩ 1)).down
      else 0 :=
  (rfl)

/-- When `i + k = n`, the coefficient at `q` of the chain of `-f` associated with a cochain `a` of
`f` of index `i` is the value of `a` on `q`. -/
theorem morseCochainToNegChain_apply_of_add_eq {i k : ℕ} (hik : i + k = finrank ℝ E)
    (a : (h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
    (q : {q : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) q = k}) :
    h.morseCochainToNegChain hf i k a q =
      (a (Finsupp.single (hf.morseIndexNegEquiv hik q) 1)).down := by
  rw [morseCochainToNegChain_apply]
  split_ifs with hq
  · -- Both are `q`, read as a critical point of index `i` for `f`.
    congr 3
    ext
    simp
  · exact absurd (by simpa using (hf.morseIndexNegEquiv hik q).2) hq

/-- Outside complementary degrees, a cochain of `f` gives the zero chain of `-f`: no critical
point has index `k` for `-f` and index `i` for `f` unless `i + k = n`. -/
theorem morseCochainToNegChain_eq_zero {i k : ℕ} (hik : i + k ≠ finrank ℝ E) :
    h.morseCochainToNegChain hf i k = 0 := by
  ext a q
  rw [morseCochainToNegChain_apply]
  split_ifs with hq
  · have := hf.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank (by simpa using q.1.2)
    exact absurd (by rw [← this, q.2, hq, add_comm]) hik
  · rfl

/-- **Cochains of `f` are chains of `-f`.** In complementary degrees `i + k = n`, reading a cochain
of `f` of index `i` as a chain of `-f` of index `k` is an isomorphism. -/
theorem bijective_morseCochainToNegChain {i k : ℕ} (hik : i + k = finrank ℝ E) :
    Function.Bijective (h.morseCochainToNegChain hf i k) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ ?_, fun c ↦ ?_⟩
  · -- A cochain vanishing at every critical point of index `i` is zero.
    refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring (ULift.ext ?_))
    have := DFunLike.congr_fun ha ((hf.morseIndexNegEquiv hik).symm p)
    rwa [morseCochainToNegChain_apply_of_add_eq h hf hik, Equiv.apply_symm_apply] at this
  · -- The cochain with the values of `c` at the critical points.
    let a : (h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)) :=
      ModuleCat.ofHom (Finsupp.linearCombination (ZMod 2)
        fun p ↦ ULift.up (c ((hf.morseIndexNegEquiv hik).symm p)))
    refine ⟨a, Finsupp.ext fun q ↦ ?_⟩
    rw [morseCochainToNegChain_apply_of_add_eq h hf hik]
    refine (congrArg ULift.down (ModuleCat.ofHom_apply _ _)).trans ?_
    simp

/-- **The coboundary of `f` is the boundary of `-f`.** Reading cochains of `f` as chains of `-f`
carries the Morse coboundary `a ↦ a ∘ ∂` of `f` from index `i` to index `i + 1` to the mod-two
Morse boundary of `-f` from index `k + 1` to index `k`. Both count, modulo two, the trajectories of
`X` between critical points of index `i + 1` and `i` for `f`. -/
theorem morseCochainToNegChain_d_comp (i k : ℕ)
    (a : (h.morseComplex hf).X i ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) :
    h.morseCochainToNegChain hf (i + 1) k ((h.morseComplex hf).d (i + 1) i ≫ a) =
      (h.neg hf).morseBoundaryAt hf.neg k (h.morseCochainToNegChain hf i (k + 1) a) := by
  have := hf.finite_criticalPoints.to_subtype
  have := hf.neg.finite_criticalPoints.to_subtype
  let _ := Fintype.ofFinite {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = i}
  let _ := Fintype.ofFinite
    {r : criticalPoints 𝓘(ℝ, E) (-f) // manifoldMorseIndex 𝓘(ℝ, E) (-f) r = k + 1}
  ext q
  rw [morseBoundaryAt_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseCochainToNegChain_apply]
  split_ifs with hqi
  · -- `q` has index `i + 1` for `f`, so the degrees `i` and `k + 1` are complementary.
    have hik : i + (k + 1) = finrank ℝ E := by
      have := hf.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank (by simpa using q.1.2)
      have := q.2
      omega
    refine (congrArg ULift.down (ModuleCat.comp_apply _ _ _)).trans ?_
    rw [morseComplex_d_apply]
    -- Expand `a` on the basis of the chains of index `i`.
    refine (congrArg ULift.down (a.hom.apply_eq_finsuppSum_smul _)).trans ?_
    rw [← ULift.moduleEquiv_apply (R := ZMod 2), map_finsuppSum,
      Finsupp.sum_fintype _ _ fun _ ↦ by simp]
    refine Fintype.sum_equiv (hf.morseIndexNegEquiv hik).symm _ _ fun p ↦ ?_
    -- After `simp`, both sides are the product of the value of `a` at `p` with the coefficient
    -- `h.morseBoundaryCoeff hf q p`, in opposite orders: `ac_rfl` commutes them. The domain of
    -- `a` is written as the Morse chains on one side and as the term of the Morse complex on the
    -- other, which agree by definition.
    simp [morseBoundaryAt_single_apply, morseCochainToNegChain_apply_of_add_eq h hf hik,
      h.morseBoundaryCoeff_neg hf]
    ac_rfl
  · -- Otherwise no trajectory of `X` joins `q` to a critical point of index `i` for `f`.
    refine (Finset.sum_eq_zero fun r _ ↦ ?_).symm
    rw [morseCochainToNegChain_apply]
    split_ifs with hri
    · rw [h.morseBoundaryCoeff_neg hf, h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf,
        mul_zero]
      simpa [hri] using hqi
    · rw [zero_mul]

/-- **Reading cochains of `f` as chains of `-f` commutes with the differentials.** It intertwines
the coboundary of the Morse cochain complex of `f` from index `i` to index `i + 1` with the
differential of the Morse chain complex of `-f` from index `k + 1` to index `k`. The maps are
bijective only in complementary degrees (`IsMorseSmale.bijective_morseCochainToNegChain`). -/
theorem morseCochainComplex_d_comp_ofHom (i k : ℕ) :
    (h.morseCochainComplex hf).d i (i + 1) ≫
        ModuleCat.ofHom (h.morseCochainToNegChain hf (i + 1) k) =
      ModuleCat.ofHom (h.morseCochainToNegChain hf i (k + 1)) ≫
        ((h.neg hf).morseComplex hf.neg).d (k + 1) k := by
  rw [(h.neg hf).morseComplex_d hf.neg]
  ext a : 2
  exact h.morseCochainToNegChain_d_comp hf i k a

/-! ### Morse cohomology of `f` is Morse homology of `-f` -/

/-- The morphism of short complexes, from the coboundaries of `f` into and out of index `i` to the
boundaries of `-f` into and out of index `k`, given by reading cochains of `f` as chains of `-f`.
For `i + k = n` it is an isomorphism in the middle, and it is an epimorphism on the left and a
monomorphism on the right, also at the ends `i = 0` and `k = 0` of the complexes. -/
private noncomputable def morseCochainToNegChainSc {i k : ℕ} (hik : i + k = finrank ℝ E) :
    (h.morseCochainComplex hf).sc' (i - 1) i (i + 1) ⟶
      ((h.neg hf).morseComplex hf.neg).sc' (k + 1) k (k - 1) where
  τ₁ := ModuleCat.ofHom (h.morseCochainToNegChain hf (i - 1) (k + 1))
  τ₂ := ModuleCat.ofHom (h.morseCochainToNegChain hf i k)
  τ₃ := ModuleCat.ofHom (h.morseCochainToNegChain hf (i + 1) (k - 1))
  comm₁₂ := by
    rcases i with _ | i
    · -- At `i = 0` no coboundary enters index `0`, and `-f` has no critical point of index `n + 1`.
      have hd : ((h.morseCochainComplex hf).sc' (0 - 1) 0 (0 + 1)).f = 0 :=
        (h.morseCochainComplex hf).shape _ _ (by simp)
      rw [hd, h.morseCochainToNegChain_eq_zero hf (by omega), ModuleCat.ofHom_zero]
      exact zero_comp.trans zero_comp.symm
    · exact (h.morseCochainComplex_d_comp_ofHom hf i k).symm
  comm₂₃ := by
    rcases k with _ | k
    · -- At `k = 0` no boundary leaves index `0`, and `f` has no critical point of index `n + 1`.
      have hd : (((h.neg hf).morseComplex hf.neg).sc' (0 + 1) 0 (0 - 1)).g = 0 :=
        ((h.neg hf).morseComplex hf.neg).shape _ _ (by simp)
      rw [hd, h.morseCochainToNegChain_eq_zero hf (i := i + 1) (k := 0 - 1) (by omega),
        ModuleCat.ofHom_zero]
      exact comp_zero.trans comp_zero.symm
    · exact (h.morseCochainComplex_d_comp_ofHom hf i k).symm

/-- **Morse cohomology of `f` is Morse homology of `-f`.** For `i + k = n`, reading cochains of `f`
as chains of `-f` identifies the mod-two Morse cohomology of `f` in degree `i` with the mod-two
Morse homology of `-f`, for the pseudo-gradient `-X`, in degree `k`. -/
noncomputable def morseCohomologyEquivNegHomology {i k : ℕ} (hik : i + k = finrank ℝ E) :
    (h.morseCochainComplex hf).homology i ≃ₗ[ZMod 2]
      ((h.neg hf).morseComplex hf.neg).homology k :=
  haveI : Epi (h.morseCochainToNegChainSc hf hik).τ₁ := by
    rcases i with _ | i
    · -- The chains of `-f` of index `n + 1` vanish.
      exact IsZero.epi ((h.neg hf).isZero_morseComplex_X_of_finrank_lt hf.neg (by omega)) _
    · exact (ModuleCat.epi_iff_surjective _).2 (h.bijective_morseCochainToNegChain hf
        (by omega)).2
  haveI : IsIso (h.morseCochainToNegChainSc hf hik).τ₂ :=
    (ConcreteCategory.isIso_iff_bijective _).2 (h.bijective_morseCochainToNegChain hf hik)
  haveI : Mono (h.morseCochainToNegChainSc hf hik).τ₃ := by
    rcases k with _ | k
    · -- The cochains of `f` of index `n + 1` vanish, since its chains of index `n + 1` do.
      refine IsZero.mono ?_ _
      rw [ModuleCat.isZero_iff_subsingleton]
      exact ⟨fun a b ↦ (h.isZero_morseComplex_X_of_finrank_lt hf (by omega)).eq_of_src a b⟩
    · exact (ModuleCat.mono_iff_injective _).2 (h.bijective_morseCochainToNegChain hf
        (by omega)).1
  ((h.morseCochainComplex hf).homologyIsoSc' (i - 1) i (i + 1)
      (by rcases i with _ | i <;> simp) (by simp) ≪≫
    asIso (ShortComplex.homologyMap (h.morseCochainToNegChainSc hf hik)) ≪≫
    (((h.neg hf).morseComplex hf.neg).homologyIsoSc' (k + 1) k (k - 1)
      (by simp) (by rcases k with _ | k <;> simp)).symm).toLinearEquiv

/-- A cocycle of `f` of index `i`, read as a chain of `-f` of index `k`, is a cycle of `-f`, for
`i + k = n`. -/
theorem iCycles_comp_ofHom_morseCochainToNegChain_comp_d {i k : ℕ}
    (hik : i + k = finrank ℝ E) :
    ((h.morseCochainComplex hf).iCycles i ≫ ModuleCat.ofHom (h.morseCochainToNegChain hf i k)) ≫
      ((h.neg hf).morseComplex hf.neg).d k (k - 1) = 0 := by
  -- Reading cochains as chains commutes with the differentials leaving index `i` and `k`.
  calc _ = (h.morseCochainComplex hf).iCycles i ≫ (h.morseCochainToNegChainSc hf hik).τ₂ ≫
        (((h.neg hf).morseComplex hf.neg).sc' (k + 1) k (k - 1)).g := Category.assoc _ _ _
    _ = (h.morseCochainComplex hf).iCycles i ≫
        ((h.morseCochainComplex hf).sc' (i - 1) i (i + 1)).g ≫
          (h.morseCochainToNegChainSc hf hik).τ₃ := by rw [ShortComplex.Hom.comm₂₃]
    _ = 0 := ((h.morseCochainComplex hf).iCycles_d_assoc _ _ _).trans zero_comp

/-- **The identification of Morse cohomology of `f` with Morse homology of `-f` on classes.** For
`i + k = n`, it sends the class of a cocycle of `f` to the class of the same cocycle read as a
cycle of `-f`. -/
theorem morseCohomologyEquivNegHomology_homologyπ {i k : ℕ} (hik : i + k = finrank ℝ E)
    (x : (h.morseCochainComplex hf).cycles i) :
    h.morseCohomologyEquivNegHomology hf hik ((h.morseCochainComplex hf).homologyπ i x) =
      ((h.neg hf).morseComplex hf.neg).homologyπ k
        (((h.neg hf).morseComplex hf.neg).liftCycles
          ((h.morseCochainComplex hf).iCycles i ≫
            ModuleCat.ofHom (h.morseCochainToNegChain hf i k))
          (k - 1) (by rcases k with _ | k <;> simp)
          (h.iCycles_comp_ofHom_morseCochainToNegChain_comp_d hf hik) x) := by
  rw [morseCohomologyEquivNegHomology, Iso.toLinearEquiv_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply]
  refine ConcreteCategory.congr_hom ?_ x
  -- Each step of the composite is induced on cycles, where it acts as `morseCochainToNegChain`.
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (((h.neg hf).morseComplex hf.neg).iCycles k)]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc,
    HomologicalComplex.liftCycles_i]
  -- The middle component of `morseCochainToNegChainSc` is `morseCochainToNegChain`.
  simp [morseCochainToNegChainSc]

/-- **The Morse homologies of `-f` and `f` in complementary degrees.** For `i + k = n`, the mod-two
Morse homology of `-f`, for the pseudo-gradient `-X`, in degree `k` has the same dimension as the
mod-two Morse homology of `f` in degree `i`. This gives mod-two Poincaré duality once Morse
homology is known to be independent of the Morse–Smale pair, which is not proved here. -/
theorem finrank_homology_morseComplex_neg {i k : ℕ} (hik : i + k = finrank ℝ E) :
    finrank (ZMod 2) (((h.neg hf).morseComplex hf.neg).homology k) =
      finrank (ZMod 2) ((h.morseComplex hf).homology i) := by
  rw [← (h.morseCohomologyEquivNegHomology hf hik).finrank_eq,
    finrank_homology_morseCochainComplex]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
