/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.End.Stable.Basic
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.Algebra.DirectSum.Exact
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.End.Prod
import TauCeti.LinearAlgebra.Pi.Map
import TauCeti.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Submodule.Prod.Basic

/-!
# Algebraic constructions on stable module endomorphisms

This file shows that stability of module endomorphisms (`Module.End.IsStableAt` and
`Module.End.IsStable`) is preserved by intertwiners, kernels, cokernels, products, and direct sums:

* **Conjugation and intertwiners:** linear equivalences intertwining two endomorphisms preserve
  `IsStableAt` and `IsStable`; arbitrary intertwining maps carry the nilpotent and invertible
  summands into the corresponding summands of the target, commute with the canonical Fitting
  projections, and induce stable endomorphisms on their kernels and cokernels (preserving a common
  stabilizing exponent `c`).
* **Products and direct sums:** binary products (`LinearMap.prodMap`), arbitrary indexed products
  (`LinearMap.piMap`), and direct sums (`DirectSum.lmap`) of endomorphisms stable at a common
  positive exponent `c` are stable at `c`; binary products also preserve `IsStable` without a
  common exponent given in advance.

Precomposition on `Hom` modules is treated in `TauCeti.LinearAlgebra.End.Stable.Hom`.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Definition 11.9 and Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

open DirectSum

namespace Module.End

section Semiring

section Intertwiner

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- Stability at `c` transfers along an intertwining linear equivalence. -/
theorem IsStableAt.of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) {c : ℕ} (h : T_M.IsStableAt c) :
    T_N.IsStableAt c := by
  have hker : LinearMap.ker (T_N ^ c) = (LinearMap.ker (T_M ^ c)).map (e : M →ₗ[R] N) :=
    (e.map_ker_of_intertwine (T_M ^ c) (T_N ^ c) fun x ↦
      LinearMap.congr_fun (Module.End.commute_pow_left_of_commute he.symm c) x).symm
  have hrange : LinearMap.range (T_N ^ c) = (LinearMap.range (T_M ^ c)).map (e : M →ₗ[R] N) :=
    (e.map_range_of_intertwine (T_M ^ c) (T_N ^ c) fun x ↦
      LinearMap.congr_fun (Module.End.commute_pow_left_of_commute he.symm c) x).symm
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  refine ⟨h.one_le, ?_, (e.bijective_restrict_iff_of_intertwine T_M T_N
    (fun x ↦ (LinearMap.congr_fun he x).symm) hrange.symm).mp h.bijective_restrict_range_pow⟩
  rw [hker, hrange]
  exact (Submodule.orderIsoMapComap e).isCompl h.isCompl_ker_pow_range_pow

/-- Two endomorphisms intertwined by a linear equivalence are stable at `c` simultaneously. -/
theorem isStableAt_iff_of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) {c : ℕ} :
    T_M.IsStableAt c ↔ T_N.IsStableAt c := by
  refine ⟨fun h ↦ h.of_linearEquiv e he, fun h ↦ h.of_linearEquiv e.symm ?_⟩
  ext y
  exact e.injective (by simpa using (LinearMap.congr_fun he (e.symm y)).symm)

/-- Two endomorphisms intertwined by a linear equivalence are stable simultaneously. -/
theorem isStable_iff_of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) :
    T_M.IsStable ↔ T_N.IsStable := by
  rw [isStable_def, isStable_def]
  exact exists_congr fun _ ↦ isStableAt_iff_of_linearEquiv e he

end Intertwiner

section ProdPiDirectSum

variable {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂]

/-- A componentwise product of two endomorphisms is stable at `c` if and only if both factors are
stable at `c`. -/
@[simp]
theorem isStableAt_prodMap_iff {T₁ : End R M₁} {T₂ : End R M₂} {c : ℕ} :
    IsStableAt (T₁.prodMap T₂) c ↔ T₁.IsStableAt c ∧ T₂.IsStableAt c := by
  have hrange : LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ c) =
      (LinearMap.range (T₁ ^ c)).prod (LinearMap.range (T₂ ^ c)) := by
    rw [LinearMap.prodMap_pow, LinearMap.range_prodMap]
  have hcompl : IsCompl (LinearMap.ker ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ c))
      (LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ c)) ↔
      IsCompl (LinearMap.ker (T₁ ^ c)) (LinearMap.range (T₁ ^ c)) ∧
        IsCompl (LinearMap.ker (T₂ ^ c)) (LinearMap.range (T₂ ^ c)) := by
    rw [LinearMap.prodMap_pow, LinearMap.ker_prodMap, LinearMap.range_prodMap,
      Submodule.isCompl_prod_iff]
  have hbij : Function.Bijective ((T₁.prodMap T₂ : End R (M₁ × M₂)).restrict
      (fun _ hx ↦ (T₁.prodMap T₂ : End R (M₁ × M₂)).mapsTo_range_pow c hx)) ↔
      Function.Bijective (T₁.restrict (fun _ hx ↦ T₁.mapsTo_range_pow c hx)) ∧
        Function.Bijective (T₂.restrict (fun _ hx ↦ T₂.mapsTo_range_pow c hx)) :=
    (LinearMap.bijective_restrict_iff_of_eq hrange
      (hq := fun _ hx ↦ ⟨T₁.mapsTo_range_pow c hx.1, T₂.mapsTo_range_pow c hx.2⟩)).trans
      LinearMap.bijective_restrict_prodMap_iff
  simp only [isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hcompl, hbij]
  tauto

/-- The componentwise product of two endomorphisms stable at `c` is stable at `c`. -/
theorem IsStableAt.prodMap {T₁ : End R M₁} {T₂ : End R M₂} {c : ℕ}
    (h₁ : T₁.IsStableAt c) (h₂ : T₂.IsStableAt c) :
    IsStableAt (T₁.prodMap T₂) c :=
  isStableAt_prodMap_iff.mpr ⟨h₁, h₂⟩

/-- A binary product of endomorphisms is stable if and only if both factors are stable. -/
@[simp]
theorem isStable_prodMap_iff {T₁ : End R M₁} {T₂ : End R M₂} :
    IsStable (T₁.prodMap T₂) ↔ T₁.IsStable ∧ T₂.IsStable := by
  rw [isStable_def, isStable_def, isStable_def]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := isStableAt_prodMap_iff.mp hc
    exact ⟨⟨c, h₁⟩, ⟨c, h₂⟩⟩
  · exact ⟨max c₁ c₂, (hc₁.mono (le_max_left _ _)).prodMap (hc₂.mono (le_max_right _ _))⟩

/-- The componentwise product of two stable endomorphisms is stable. -/
theorem IsStable.prodMap {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : T₁.IsStable) (h₂ : T₂.IsStable) :
    IsStable (T₁.prodMap T₂) :=
  isStable_prodMap_iff.mpr ⟨h₁, h₂⟩

/-- The eventual kernel of `T₁.prodMap T₂` is the product of the eventual kernels of `T₁` and
`T₂`. -/
theorem iSup_ker_pow_prodMap (T₁ : End R M₁) (T₂ : End R M₂) :
    (⨆ n, LinearMap.ker ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) =
      (⨆ n, LinearMap.ker (T₁ ^ n)).prod (⨆ n, LinearMap.ker (T₂ ^ n)) := by
  simp only [LinearMap.prodMap_pow, LinearMap.ker_prodMap, TauCeti.iSup_prod_submodule]

/-- The stable range of `T₁.prodMap T₂` is the product of the stable ranges of `T₁` and `T₂`. -/
theorem iInf_range_pow_prodMap (T₁ : End R M₁) (T₂ : End R M₂) :
    (⨅ n, LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) =
      (⨅ n, LinearMap.range (T₁ ^ n)).prod (⨅ n, LinearMap.range (T₂ ^ n)) := by
  ext ⟨x, y⟩
  simp only [LinearMap.prodMap_pow, LinearMap.range_prodMap, Submodule.mem_iInf, Submodule.mem_prod]
  exact forall_and

/-- On `M₁ × M₂`, when `T₁` is nilpotent and `T₂` is bijective, the nilpotent summand
`⨆ n, ker ((T₁.prodMap T₂) ^ n)` is the first factor `Submodule.fst R M₁ M₂`. -/
theorem iSup_ker_pow_prodMap_of_isNilpotent_of_bijective {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂) :
    (⨆ n, LinearMap.ker ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) = Submodule.fst R M₁ M₂ := by
  obtain ⟨c, hc⟩ := h₁
  have hk₁ : (⨆ n, LinearMap.ker (T₁ ^ n)) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ Submodule.mem_iSup_of_mem c (by simp [hc])
  have hk₂ : (⨆ n, LinearMap.ker (T₂ ^ n)) = ⊥ :=
    eq_bot_iff.mpr <| iSup_le fun n x hx ↦
      h₂.injective.iterate n (by simpa [pow_apply_eq_iterate] using LinearMap.mem_ker.mp hx)
  rw [iSup_ker_pow_prodMap, hk₁, hk₂]
  ext ⟨x, y⟩
  simp

/-- On `M₁ × M₂`, when `T₁` is nilpotent and `T₂` is bijective, the stable range
`⨅ n, range ((T₁.prodMap T₂) ^ n)` is the second factor `Submodule.snd R M₁ M₂`. -/
theorem iInf_range_pow_prodMap_of_isNilpotent_of_bijective {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : IsNilpotent T₁) (h₂ : Function.Bijective T₂) :
    (⨅ n, LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) = Submodule.snd R M₁ M₂ := by
  obtain ⟨c, hc⟩ := h₁
  have hr₁ : (⨅ n, LinearMap.range (T₁ ^ n)) = ⊥ :=
    eq_bot_iff.mpr <| (iInf_le _ c).trans (by simp [hc])
  have hr₂ : (⨅ n, LinearMap.range (T₂ ^ n)) = ⊤ :=
    eq_top_iff.mpr <| le_iInf fun n y _ ↦ by
      obtain ⟨x, hx⟩ := h₂.surjective.iterate n y
      exact ⟨x, by simpa [pow_apply_eq_iterate] using hx⟩
  rw [iInf_range_pow_prodMap, hr₁, hr₂]
  ext ⟨x, y⟩
  simp

section Indexed

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- A coordinatewise endomorphism `LinearMap.piMap T` on `∀ i, M i` is stable at `c` if and only if
`1 ≤ c` and every coordinate `T i` is stable at `c`. -/
@[simp]
theorem isStableAt_piMap_iff {T : ∀ i, End R (M i)} {c : ℕ} :
    IsStableAt (LinearMap.piMap T) c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c := by
  have hrange : LinearMap.range ((LinearMap.piMap T : End R (∀ i, M i)) ^ c) =
      Submodule.pi Set.univ fun i ↦ LinearMap.range ((T i) ^ c) := by
    rw [LinearMap.piMap_pow, LinearMap.range_piMap]
  have hcompl : IsCompl (LinearMap.ker ((LinearMap.piMap T : End R (∀ i, M i)) ^ c))
      (LinearMap.range ((LinearMap.piMap T : End R (∀ i, M i)) ^ c)) ↔
      ∀ i, IsCompl (LinearMap.ker ((T i) ^ c)) (LinearMap.range ((T i) ^ c)) := by
    rw [LinearMap.piMap_pow, LinearMap.ker_piMap, LinearMap.range_piMap,
      Submodule.isCompl_pi_univ_iff]
  have hbij : Function.Bijective ((LinearMap.piMap T : End R (∀ i, M i)).restrict
      (fun _ hx ↦ (LinearMap.piMap T : End R (∀ i, M i)).mapsTo_range_pow c hx)) ↔
      ∀ i, Function.Bijective ((T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx)) :=
    (LinearMap.bijective_restrict_iff_of_eq hrange
      (hq := fun _ hx i hi ↦ (T i).mapsTo_range_pow c (hx i hi))).trans
      LinearMap.bijective_restrict_piMap_iff
  simp only [isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hcompl, hbij]
  exact ⟨fun ⟨hc, h₁, h₂⟩ ↦ ⟨hc, fun i ↦ ⟨hc, h₁ i, h₂ i⟩⟩,
    fun ⟨hc, h⟩ ↦ ⟨hc, fun i ↦ (h i).2.1, fun i ↦ (h i).2.2⟩⟩

/-- A coordinatewise product of endomorphisms stable at a common positive exponent `c` is stable
at `c`. -/
theorem IsStableAt.piMap {T : ∀ i, End R (M i)} {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ i, (T i).IsStableAt c) :
    IsStableAt (LinearMap.piMap T) c :=
  isStableAt_piMap_iff.mpr ⟨hc, h⟩

/-- A direct-sum endomorphism `DirectSum.lmap T` on `⨁ i, M i` is stable at `c` if and only if
`1 ≤ c` and every summand `T i` is stable at `c`. -/
@[simp]
theorem isStableAt_lmap_iff {T : ∀ i, End R (M i)} {c : ℕ} :
    IsStableAt (DirectSum.lmap T) c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c := by
  have hrange : LinearMap.range ((DirectSum.lmap T : End R (⨁ i, M i)) ^ c) =
      TauCeti.DirectSum.piSubmodule fun i ↦ LinearMap.range ((T i) ^ c) := by
    rw [DirectSum.lmap_pow, DirectSum.range_lmap, TauCeti.DirectSum.comap_coeFnLinearMap_pi_univ]
  have hcompl : IsCompl (LinearMap.ker ((DirectSum.lmap T : End R (⨁ i, M i)) ^ c))
      (LinearMap.range ((DirectSum.lmap T : End R (⨁ i, M i)) ^ c)) ↔
      ∀ i, IsCompl (LinearMap.ker ((T i) ^ c)) (LinearMap.range ((T i) ^ c)) := by
    rw [DirectSum.lmap_pow, DirectSum.ker_lmap, DirectSum.range_lmap,
      TauCeti.DirectSum.comap_coeFnLinearMap_pi_univ,
      TauCeti.DirectSum.comap_coeFnLinearMap_pi_univ,
      TauCeti.DirectSum.isCompl_piSubmodule_iff]
  have hbij : Function.Bijective ((DirectSum.lmap T : End R (⨁ i, M i)).restrict
      (fun _ hx ↦ (DirectSum.lmap T : End R (⨁ i, M i)).mapsTo_range_pow c hx)) ↔
      ∀ i, Function.Bijective ((T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx)) :=
    (LinearMap.bijective_restrict_iff_of_eq hrange
      (hq := fun x hx ↦ (TauCeti.DirectSum.mem_piSubmodule_iff _ _).mpr fun i ↦
        (T i).mapsTo_range_pow c ((TauCeti.DirectSum.mem_piSubmodule_iff _ _).mp hx i))).trans
      TauCeti.DirectSum.bijective_restrict_lmap_iff
  simp only [isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hcompl, hbij]
  exact ⟨fun ⟨hc, h₁, h₂⟩ ↦ ⟨hc, fun i ↦ ⟨hc, h₁ i, h₂ i⟩⟩,
    fun ⟨hc, h⟩ ↦ ⟨hc, fun i ↦ (h i).2.1, fun i ↦ (h i).2.2⟩⟩

/-- A direct sum of endomorphisms stable at a common positive exponent `c` is stable at `c`. -/
theorem IsStableAt.lmap {T : ∀ i, End R (M i)} {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ i, (T i).IsStableAt c) :
    IsStableAt (DirectSum.lmap T) c :=
  isStableAt_lmap_iff.mpr ⟨hc, h⟩

end Indexed

end ProdPiDirectSum

end Semiring

section Ring

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- An equivariant linear map between stable operators commutes with the Fitting projections onto
the nilpotent summands `⨆ k, ker (T ^ k)`. -/
theorem IsStable.comp_projection_iSup_ker_pow {T_M : End R M} {T_N : End R N}
    (hM : T_M.IsStable) (hN : T_N.IsStable) {f : M →ₗ[R] N} (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    f ∘ₗ (⨆ k, LinearMap.ker (T_M ^ k)).projection (⨅ k, LinearMap.range (T_M ^ k))
        hM.isCompl_iSup_ker_pow_iInf_range_pow =
      (⨆ k, LinearMap.ker (T_N ^ k)).projection (⨅ k, LinearMap.range (T_N ^ k))
        hN.isCompl_iSup_ker_pow_iInf_range_pow ∘ₗ f :=
  Submodule.comp_projection_of_map_le _ _ (map_iSup_ker_pow_le_of_comp_eq hf)
    (map_iInf_range_pow_le_of_comp_eq hf)

/-- An equivariant linear map between stable operators commutes with the Fitting projections onto
the invertible summands `⨅ k, range (T ^ k)`. -/
theorem IsStable.comp_projection_iInf_range_pow {T_M : End R M} {T_N : End R N}
    (hM : T_M.IsStable) (hN : T_N.IsStable) {f : M →ₗ[R] N} (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    f ∘ₗ (⨅ k, LinearMap.range (T_M ^ k)).projection (⨆ k, LinearMap.ker (T_M ^ k))
        hM.isCompl_iSup_ker_pow_iInf_range_pow.symm =
      (⨅ k, LinearMap.range (T_N ^ k)).projection (⨆ k, LinearMap.ker (T_N ^ k))
        hN.isCompl_iSup_ker_pow_iInf_range_pow.symm ∘ₗ f :=
  Submodule.comp_projection_of_map_le _ _ (map_iInf_range_pow_le_of_comp_eq hf)
    (map_iSup_ker_pow_le_of_comp_eq hf)

/-- If `T_M` and `T_N` are both stable at `c`, the restriction of `T_M` to the kernel of an
intertwiner `f : M →ₗ[R] N` is also stable at `c`. -/
theorem IsStableAt.restrict_ker_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) {c : ℕ} (hM : T_M.IsStableAt c) (hN : T_N.IsStableAt c) :
    IsStableAt (T_M.restrict fun _ hx ↦ LinearMap.map_mem_ker_of_comp_eq T_M hf.symm hx) c := by
  let TK := T_M.restrict fun _ hx ↦ LinearMap.map_mem_ker_of_comp_eq T_M hf.symm hx
  have hrange_ge : ∀ x : ↥(LinearMap.ker f), x.val ∈ LinearMap.range (T_M ^ c) →
      x ∈ LinearMap.range (TK ^ c) := by
    rintro x ⟨y, hy⟩
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hM.isCompl_ker_pow_range_pow.codisjoint y
    have hfv_ker : f v ∈ LinearMap.ker (T_N ^ c) := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
        Module.End.commute_pow_left_of_commute hf.symm c, LinearMap.comp_apply]
      have hTMv : (T_M ^ c) v = x.val := by
        rw [← hy, map_add, LinearMap.mem_ker.mp hu, zero_add]
      rw [hTMv, LinearMap.mem_ker.mp x.property]
    have hfv0 : f v = 0 := Submodule.disjoint_def.mp hN.isCompl_ker_pow_range_pow.disjoint _
      hfv_ker (map_range_pow_le_of_comp_eq hf c ⟨v, hv, rfl⟩)
    refine ⟨⟨v, LinearMap.mem_ker.mpr hfv0⟩, Subtype.ext ?_⟩
    rw [pow_restrict c, LinearMap.coe_restrict_apply, ← hy, map_add,
      LinearMap.mem_ker.mp hu, zero_add]
  rw [isStableAt_iff_isCompl_ker_pow_range_pow]
  refine ⟨hM.one_le, Submodule.disjoint_def.mpr fun x hxk hxr ↦ ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun x ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hxr
    have hxk' : (T_M ^ c) ((TK ^ c) z).val = 0 := by
      simpa [TK, pow_restrict c] using congrArg Subtype.val (LinearMap.mem_ker.mp hxk)
    have hzM : ((TK ^ c) z).val ∈ LinearMap.range (T_M ^ c) :=
      ⟨z.val, by simp [TK, pow_restrict c]⟩
    exact Subtype.ext (Submodule.disjoint_def.mp hM.isCompl_ker_pow_range_pow.disjoint _
      (LinearMap.mem_ker.mpr hxk') hzM)
  · obtain ⟨u, v, hu, hv, huv⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hM.isCompl_ker_pow_range_pow.codisjoint x.val
    have hfu_eq : f u = -f v := eq_neg_of_add_eq_zero_left <| by
      rw [← map_add, huv, LinearMap.mem_ker.mp x.property]
    have hfu0 : f u = 0 := Submodule.disjoint_def.mp hN.isCompl_ker_pow_range_pow.disjoint _
      (map_ker_pow_le_of_comp_eq hf c ⟨u, hu, rfl⟩)
      (hfu_eq ▸ neg_mem (map_range_pow_le_of_comp_eq hf c ⟨v, hv, rfl⟩))
    have hfv0 : f v = 0 := neg_inj.mp (by rw [← hfu_eq, hfu0, neg_zero])
    refine ⟨⟨u, LinearMap.mem_ker.mpr hfu0⟩, ⟨v, LinearMap.mem_ker.mpr hfv0⟩, ?_,
      hrange_ge _ hv, Subtype.ext huv⟩
    rw [LinearMap.mem_ker, pow_restrict c]
    exact Subtype.ext (LinearMap.mem_ker.mp hu)

/-- The restriction of a stable endomorphism to the kernel of an intertwiner into a stable
endomorphism is stable. -/
theorem IsStable.restrict_ker_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (hM : T_M.IsStable) (hN : T_N.IsStable) :
    IsStable (T_M.restrict fun _ hx ↦ LinearMap.map_mem_ker_of_comp_eq T_M hf.symm hx) := by
  rw [isStable_def] at hM hN ⊢
  obtain ⟨c₁, hc₁⟩ := hM
  obtain ⟨c₂, hc₂⟩ := hN
  exact ⟨max c₁ c₂, IsStableAt.restrict_ker_of_comp_eq hf
    (hc₁.mono (le_max_left _ _)) (hc₂.mono (le_max_right _ _))⟩

private theorem ker_mapQ_range_pow_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) {c : ℕ} (hM : T_M.IsStableAt c) (hN : T_N.IsStableAt c) :
    LinearMap.ker
        (((LinearMap.range f).mapQ (LinearMap.range f) T_N
          (LinearMap.range_le_comap_range_of_comp_eq hf.symm)) ^ c) =
      (LinearMap.ker (T_N ^ c)).map (LinearMap.range f).mkQ := by
  set Rf := LinearMap.range f
  set TQ := Rf.mapQ Rf T_N (LinearMap.range_le_comap_range_of_comp_eq hf.symm)
  have hpow : TQ ^ c = Rf.mapQ Rf (T_N ^ c)
      (Rf.le_comap_pow_of_le_comap (LinearMap.range_le_comap_range_of_comp_eq hf.symm) c) :=
    (Rf.mapQ_pow (LinearMap.range_le_comap_range_of_comp_eq hf.symm) c).symm
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Rf z
    have hy : (T_N ^ c) y ∈ Rf := by
      rw [← Submodule.ker_mkQ Rf, LinearMap.mem_ker]
      simpa [TQ, hpow] using LinearMap.mem_ker.mp hz
    obtain ⟨m, hm⟩ := hy
    obtain ⟨u, _, hu, ⟨w, rfl⟩, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hM.isCompl_ker_pow_range_pow.codisjoint m
    have hyw : y - f w ∈ LinearMap.ker (T_N ^ (c + c)) := by
      have hfw : (T_N ^ c) (f w) = f ((T_M ^ c) w) :=
        LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf.symm c) w
      have h1 : (T_N ^ c) (y - f w) = f u := by
        rw [map_sub, ← hm, map_add, hfw, add_sub_cancel_right]
      rw [LinearMap.mem_ker, pow_add, mul_apply_eq_comp, h1, ← LinearMap.comp_apply,
        Module.End.commute_pow_left_of_commute hf.symm c, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hu, map_zero]
    rw [hN.ker_pow_eq_of_le (Nat.le_add_right c c)] at hyw
    exact ⟨y - f w, hyw, by simp [Rf]⟩
  · rintro _ ⟨y, hy, rfl⟩
    simp [TQ, hpow, LinearMap.mem_ker.mp hy]

/-- If `T_M` and `T_N` are both stable at `c`, the endomorphism induced by `T_N` on the cokernel
`N ⧸ LinearMap.range f` of an intertwiner `f : M →ₗ[R] N` is also stable at `c`. -/
theorem IsStableAt.mapQ_range_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) {c : ℕ} (hM : T_M.IsStableAt c) (hN : T_N.IsStableAt c) :
    IsStableAt
      ((LinearMap.range f).mapQ (LinearMap.range f) T_N
        (LinearMap.range_le_comap_range_of_comp_eq hf.symm)) c := by
  set Rf := LinearMap.range f
  set TQ := Rf.mapQ Rf T_N (LinearMap.range_le_comap_range_of_comp_eq hf.symm)
  have hrange : LinearMap.range (TQ ^ c) = (LinearMap.range (T_N ^ c)).map Rf.mkQ := by
    rw [← Rf.mapQ_pow (LinearMap.range_le_comap_range_of_comp_eq hf.symm) c, Submodule.range_mapQ]
  rw [isStableAt_iff_isCompl_ker_pow_range_pow, ker_mapQ_range_pow_of_comp_eq hf hM hN, hrange]
  refine ⟨hM.one_le, Submodule.disjoint_def.mpr ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ ⟨r, hr, hkr⟩
    have hsub : k - r ∈ Rf := by
      rw [← Submodule.ker_mkQ Rf, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hkr.symm
    obtain ⟨m, hm⟩ := hsub
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hM.isCompl_ker_pow_range_pow.codisjoint m
    have hkfu : k - f u = r + f v := by
      have hk_eq : k = f (u + v) + r := sub_eq_iff_eq_add.mp hm.symm
      rw [hk_eq, map_add, add_assoc, add_sub_cancel_left, add_comm]
    have h0 : k - f u = 0 := Submodule.disjoint_def.mp hN.isCompl_ker_pow_range_pow.disjoint _
      (sub_mem hk (map_ker_pow_le_of_comp_eq hf c ⟨u, hu, rfl⟩))
      (hkfu ▸ add_mem hr (map_range_pow_le_of_comp_eq hf c ⟨v, hv, rfl⟩))
    rw [sub_eq_zero.mp h0]
    exact (Submodule.Quotient.mk_eq_zero Rf).mpr (LinearMap.mem_range_self f u)
  · rw [codisjoint_iff, ← Submodule.map_sup, hN.isCompl_ker_pow_range_pow.sup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

/-- The endomorphism induced on the cokernel of an intertwiner between stable endomorphisms is
stable. -/
theorem IsStable.mapQ_range_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (hM : T_M.IsStable) (hN : T_N.IsStable) :
    IsStable ((LinearMap.range f).mapQ (LinearMap.range f) T_N
      (LinearMap.range_le_comap_range_of_comp_eq hf.symm)) := by
  rw [isStable_def] at hM hN ⊢
  obtain ⟨c₁, hc₁⟩ := hM
  obtain ⟨c₂, hc₂⟩ := hN
  exact ⟨max c₁ c₂, IsStableAt.mapQ_range_of_comp_eq hf
    (hc₁.mono (le_max_left _ _)) (hc₂.mono (le_max_right _ _))⟩

end Ring

end Module.End

end
