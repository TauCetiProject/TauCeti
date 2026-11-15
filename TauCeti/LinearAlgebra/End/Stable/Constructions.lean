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
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.Submodule.Prod

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
  positive exponent `c` are stable at `c`; binary products over a ring also preserve `IsStable`
  without a common exponent given in advance.

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

theorem map_ker_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (k : ℕ) :
    (LinearMap.ker (T_M ^ k)).map f ≤ LinearMap.ker (T_N ^ k) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
    Module.End.commute_pow_left_of_commute hf.symm k, LinearMap.comp_apply,
    LinearMap.mem_ker.mp hx, map_zero]

theorem map_range_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (k : ℕ) :
    (LinearMap.range (T_M ^ k)).map f ≤ LinearMap.range (T_N ^ k) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨f x, LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf.symm k) x⟩

theorem map_iSup_ker_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    (⨆ k, LinearMap.ker (T_M ^ k)).map f ≤ ⨆ k, LinearMap.ker (T_N ^ k) := by
  rw [Submodule.map_iSup]
  exact iSup_mono fun k ↦ map_ker_pow_le_of_comp_eq hf k

theorem map_iInf_range_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    (⨅ k, LinearMap.range (T_M ^ k)).map f ≤ ⨅ k, LinearMap.range (T_N ^ k) :=
  le_iInf fun k ↦ (Submodule.map_mono (iInf_le _ k)).trans (map_range_pow_le_of_comp_eq hf k)

/-- Stability at `c` transfers along an intertwining linear equivalence. -/
theorem IsStableAt.of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) {c : ℕ} (h : T_M.IsStableAt c) :
    T_N.IsStableAt c := by
  have hker : LinearMap.ker (T_N ^ c) = (LinearMap.ker (T_M ^ c)).map e.toLinearMap :=
    (e.map_ker_of_intertwine (T_M ^ c) (T_N ^ c) fun x ↦
      LinearMap.congr_fun (Module.End.commute_pow_left_of_commute he.symm c) x).symm
  have hrange : LinearMap.range (T_N ^ c) = (LinearMap.range (T_M ^ c)).map e.toLinearMap :=
    (e.map_range_of_intertwine (T_M ^ c) (T_N ^ c) fun x ↦
      LinearMap.congr_fun (Module.End.commute_pow_left_of_commute he.symm c) x).symm
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  refine ⟨h.one_le, ?_, ?_⟩
  · rw [hker, hrange]
    exact (Submodule.orderIsoMapComap e).isCompl h.isCompl_ker_pow_range_pow
  · constructor
    · intro x y hxy
      have hx' : x.1 ∈ (LinearMap.range (T_M ^ c)).map e.toLinearMap := hrange ▸ x.2
      have hy' : y.1 ∈ (LinearMap.range (T_M ^ c)).map e.toLinearMap := hrange ▸ y.2
      obtain ⟨x₀, hx₀, hxEq⟩ := hx'
      obtain ⟨y₀, hy₀, hyEq⟩ := hy'
      let xM : ↥(LinearMap.range (T_M ^ c)) := ⟨e.symm x.1, by simpa [← hxEq] using hx₀⟩
      let yM : ↥(LinearMap.range (T_M ^ c)) := ⟨e.symm y.1, by simpa [← hyEq] using hy₀⟩
      have hval : T_N x.1 = T_N y.1 := congrArg Subtype.val hxy
      have hTM : T_M xM.1 = T_M yM.1 := e.injective <| by
        have h1 : e (T_M xM.1) = T_N x.1 := by
          simpa [xM, LinearMap.comp_apply] using LinearMap.congr_fun he (e.symm x.1)
        have h2 : e (T_M yM.1) = T_N y.1 := by
          simpa [yM, LinearMap.comp_apply] using LinearMap.congr_fun he (e.symm y.1)
        exact h1.trans (hval.trans h2.symm)
      have hsub : xM = yM := h.bijective_restrict_range_pow.injective (Subtype.ext hTM)
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hsub))
    · intro y
      have hy' : y.1 ∈ (LinearMap.range (T_M ^ c)).map e.toLinearMap := hrange ▸ y.2
      obtain ⟨y₀, hy₀, hyEq⟩ := hy'
      obtain ⟨z₀, hz₀⟩ := h.bijective_restrict_range_pow.surjective ⟨y₀, hy₀⟩
      have hez : e z₀.1 ∈ LinearMap.range (T_N ^ c) := by
        rw [hrange]
        exact ⟨z₀.1, z₀.2, rfl⟩
      refine ⟨⟨e z₀.1, hez⟩, Subtype.ext ?_⟩
      have hzval : T_M z₀.1 = y₀ := congrArg Subtype.val hz₀
      have he_comm : e (T_M z₀.1) = T_N (e z₀.1) := LinearMap.congr_fun he z₀.1
      change T_N (e z₀.1) = y.1
      rw [← he_comm, hzval]
      exact hyEq

theorem isStableAt_iff_of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) {c : ℕ} :
    T_M.IsStableAt c ↔ T_N.IsStableAt c := by
  refine ⟨fun h ↦ h.of_linearEquiv e he, fun h ↦ h.of_linearEquiv e.symm ?_⟩
  ext y
  exact e.injective (by simpa using (LinearMap.congr_fun he (e.symm y)).symm)

theorem isStable_iff_of_linearEquiv {T_M : End R M} {T_N : End R N} (e : M ≃ₗ[R] N)
    (he : e.toLinearMap ∘ₗ T_M = T_N ∘ₗ e.toLinearMap) :
    T_M.IsStable ↔ T_N.IsStable := by
  rw [isStable_def, isStable_def]
  exact exists_congr fun _ ↦ isStableAt_iff_of_linearEquiv e he

end Intertwiner

section ProdPiDirectSum

variable {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂]

private theorem isCompl_prod_iff {p₁ q₁ : Submodule R M₁} {p₂ q₂ : Submodule R M₂} :
    IsCompl (p₁.prod p₂) (q₁.prod q₂) ↔ IsCompl p₁ q₁ ∧ IsCompl p₂ q₂ := by
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, Submodule.prod_inf_prod,
    Submodule.prod_sup_prod, Submodule.prod_eq_bot_iff, Submodule.prod_eq_top_iff]
  tauto

/-- A componentwise product of two endomorphisms is stable at `c` if and only if both factors are
stable at `c`. -/
@[simp]
theorem isStableAt_prodMap_iff {T₁ : End R M₁} {T₂ : End R M₂} {c : ℕ} :
    IsStableAt (T₁.prodMap T₂) c ↔ T₁.IsStableAt c ∧ T₂.IsStableAt c := by
  let P : End R (M₁ × M₂) := T₁.prodMap T₂
  have hmem : ∀ p : M₁ × M₂, p ∈ LinearMap.range (P ^ c) ↔
      p.1 ∈ LinearMap.range (T₁ ^ c) ∧ p.2 ∈ LinearMap.range (T₂ ^ c) := fun p ↦ by
    rw [prodMap_pow, LinearMap.range_prodMap, Submodule.mem_prod]
  have hcompl : IsCompl (LinearMap.ker (P ^ c)) (LinearMap.range (P ^ c)) ↔
      IsCompl (LinearMap.ker (T₁ ^ c)) (LinearMap.range (T₁ ^ c)) ∧
        IsCompl (LinearMap.ker (T₂ ^ c)) (LinearMap.range (T₂ ^ c)) := by
    change IsCompl (LinearMap.ker (T₁.prodMap T₂ ^ c)) (LinearMap.range (T₁.prodMap T₂ ^ c)) ↔ _
    rw [prodMap_pow, LinearMap.ker_prodMap, LinearMap.range_prodMap, isCompl_prod_iff]
  change P.IsStableAt c ↔ T₁.IsStableAt c ∧ T₂.IsStableAt c
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow,
    isStableAt_iff_isCompl_and_bijective_restrict_range_pow,
    isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hcompl]
  refine ⟨fun ⟨hc, ⟨hc₁, hc₂⟩, hbij⟩ ↦ ⟨⟨hc, hc₁, fun x y hxy ↦ ?_, fun y ↦ ?_⟩,
      ⟨hc, hc₂, fun x y hxy ↦ ?_, fun y ↦ ?_⟩⟩,
    fun ⟨⟨hc, hc₁, hb₁⟩, ⟨_, hc₂, hb₂⟩⟩ ↦ ⟨hc, ⟨hc₁, hc₂⟩,
      fun x y hxy ↦ Subtype.ext (Prod.ext ?_ ?_), fun y ↦ ?_⟩⟩
  · have h0 : P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨(x.1, 0), (hmem _).mpr ⟨x.2, zero_mem _⟩⟩ =
        P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨(y.1, 0), (hmem _).mpr ⟨y.2, zero_mem _⟩⟩ :=
      Subtype.ext (Prod.ext (congrArg Subtype.val hxy) rfl)
    exact Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) (hbij.1 h0))
  · obtain ⟨z, hz⟩ := hbij.2 ⟨(y.1, 0), (hmem _).mpr ⟨y.2, zero_mem _⟩⟩
    exact ⟨⟨z.1.1, ((hmem z.1).mp z.2).1⟩, Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) hz)⟩
  · have h0 : P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨(0, x.1), (hmem _).mpr ⟨zero_mem _, x.2⟩⟩ =
        P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨(0, y.1), (hmem _).mpr ⟨zero_mem _, y.2⟩⟩ :=
      Subtype.ext (Prod.ext rfl (congrArg Subtype.val hxy))
    exact Subtype.ext (congrArg (Prod.snd ∘ Subtype.val) (hbij.1 h0))
  · obtain ⟨z, hz⟩ := hbij.2 ⟨(0, y.1), (hmem _).mpr ⟨zero_mem _, y.2⟩⟩
    exact ⟨⟨z.1.2, ((hmem z.1).mp z.2).2⟩, Subtype.ext (congrArg (Prod.snd ∘ Subtype.val) hz)⟩
  · let a₁ : ↥(LinearMap.range (T₁ ^ c)) := ⟨x.1.1, ((hmem x.1).mp x.2).1⟩
    let b₁ : ↥(LinearMap.range (T₁ ^ c)) := ⟨y.1.1, ((hmem y.1).mp y.2).1⟩
    have h1 : T₁.restrict (fun _ hx ↦ T₁.mapsTo_range_pow c hx) a₁ =
        T₁.restrict (fun _ hx ↦ T₁.mapsTo_range_pow c hx) b₁ :=
      Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) hxy)
    exact congrArg Subtype.val (hb₁.1 h1)
  · let a₂ : ↥(LinearMap.range (T₂ ^ c)) := ⟨x.1.2, ((hmem x.1).mp x.2).2⟩
    let b₂ : ↥(LinearMap.range (T₂ ^ c)) := ⟨y.1.2, ((hmem y.1).mp y.2).2⟩
    have h2 : T₂.restrict (fun _ hx ↦ T₂.mapsTo_range_pow c hx) a₂ =
        T₂.restrict (fun _ hx ↦ T₂.mapsTo_range_pow c hx) b₂ :=
      Subtype.ext (congrArg (Prod.snd ∘ Subtype.val) hxy)
    exact congrArg Subtype.val (hb₂.1 h2)
  · obtain ⟨z₁, hz₁⟩ := hb₁.2 ⟨y.1.1, ((hmem y.1).mp y.2).1⟩
    obtain ⟨z₂, hz₂⟩ := hb₂.2 ⟨y.1.2, ((hmem y.1).mp y.2).2⟩
    exact ⟨⟨(z₁.1, z₂.1), (hmem _).mpr ⟨z₁.2, z₂.2⟩⟩,
      Subtype.ext (Prod.ext (congrArg Subtype.val hz₁) (congrArg Subtype.val hz₂))⟩

theorem IsStableAt.prodMap {T₁ : End R M₁} {T₂ : End R M₂} {c : ℕ}
    (h₁ : T₁.IsStableAt c) (h₂ : T₂.IsStableAt c) :
    IsStableAt (T₁.prodMap T₂) c :=
  isStableAt_prodMap_iff.mpr ⟨h₁, h₂⟩

theorem iSup_ker_pow_prodMap (T₁ : End R M₁) (T₂ : End R M₂) :
    (⨆ n, LinearMap.ker ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) =
      (⨆ n, LinearMap.ker (T₁ ^ n)).prod (⨆ n, LinearMap.ker (T₂ ^ n)) := by
  simp only [prodMap_pow, LinearMap.ker_prodMap, TauCeti.iSup_prod_submodule]

theorem iInf_range_pow_prodMap (T₁ : End R M₁) (T₂ : End R M₂) :
    (⨅ n, LinearMap.range ((T₁.prodMap T₂ : End R (M₁ × M₂)) ^ n)) =
      (⨅ n, LinearMap.range (T₁ ^ n)).prod (⨅ n, LinearMap.range (T₂ ^ n)) := by
  ext ⟨x, y⟩
  simp only [prodMap_pow, LinearMap.range_prodMap, Submodule.mem_iInf, Submodule.mem_prod]
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

@[simp]
theorem piMap_pow (T : ∀ i, End R (M i)) (n : ℕ) :
    (LinearMap.piMap T : End R (∀ i, M i)) ^ n = LinearMap.piMap fun i ↦ (T i) ^ n := by
  induction n with
  | zero => ext x i; rfl
  | succ n ih =>
    rw [pow_succ, ih]
    ext x i
    rfl

private theorem single_mem_pi_univ [DecidableEq ι] (p : ∀ i, Submodule R (M i)) (i : ι) {v : M i}
    (hv : v ∈ p i) :
    Pi.single i v ∈ Submodule.pi Set.univ p := fun j _ ↦ by
  rcases eq_or_ne j i with rfl | hji
  · simpa using hv
  · simp [hji]

private theorem isCompl_pi_univ_iff {p q : ∀ i, Submodule R (M i)} :
    IsCompl (Submodule.pi Set.univ p) (Submodule.pi Set.univ q) ↔
      ∀ i, IsCompl (p i) (q i) := by
  classical
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, eq_bot_iff, eq_top_iff]
  refine ⟨fun ⟨hdisj, hcod⟩ i ↦ ⟨fun v hv ↦ ?_, fun v _ ↦ ?_⟩,
    fun h ↦ ⟨fun x hx ↦ funext fun i ↦
      (h i).1 ⟨hx.1 i trivial, hx.2 i trivial⟩, fun x _ ↦ ?_⟩⟩
  · simpa using congrFun (hdisj ⟨single_mem_pi_univ p i hv.1, single_mem_pi_univ q i hv.2⟩) i
  · obtain ⟨u, hu, w, hw, hEq⟩ :=
      Submodule.mem_sup.mp (hcod (x := Pi.single i v) Submodule.mem_top)
    exact Submodule.mem_sup.mpr ⟨u i, hu i trivial, w i, hw i trivial,
      by simpa using congrFun hEq i⟩
  · have hsup : ∀ i, ∃ u ∈ p i, ∃ w ∈ q i, u + w = x i :=
      fun i ↦ Submodule.mem_sup.mp ((h i).2 Submodule.mem_top)
    choose u hu w hw huw using hsup
    exact Submodule.mem_sup.mpr ⟨u, fun i _ ↦ hu i, w, fun i _ ↦ hw i, funext huw⟩

/-- A coordinatewise endomorphism `LinearMap.piMap T` on `∀ i, M i` is stable at `c` if and only if
`1 ≤ c` and every coordinate `T i` is stable at `c`. -/
@[simp]
theorem isStableAt_piMap_iff {T : ∀ i, End R (M i)} {c : ℕ} :
    IsStableAt (LinearMap.piMap T) c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c := by
  classical
  let P : End R (∀ i, M i) := LinearMap.piMap T
  have hker : LinearMap.ker (P ^ c) = Submodule.pi Set.univ fun i ↦ LinearMap.ker ((T i) ^ c) := by
    ext x; simp [P, piMap_pow, Submodule.mem_pi, funext_iff]
  have hrange :
      LinearMap.range (P ^ c) = Submodule.pi Set.univ fun i ↦ LinearMap.range ((T i) ^ c) := by
    ext x
    simp only [P, piMap_pow, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.coe_piMap, Pi.map_apply, funext_iff]
    exact ⟨fun ⟨y, hy⟩ i ↦ ⟨y i, hy i⟩, fun h ↦ ⟨fun i ↦ (h i).choose, fun i ↦ (h i).choose_spec⟩⟩
  have hmem : ∀ x : ∀ i, M i, x ∈ LinearMap.range (P ^ c) ↔
      ∀ i, x i ∈ LinearMap.range ((T i) ^ c) := fun x ↦ by rw [hrange, Submodule.mem_pi]; simp
  change P.IsStableAt c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  simp only [isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hker, hrange,
    isCompl_pi_univ_iff]
  refine ⟨fun ⟨hc, hcompl, hbij⟩ ↦ ⟨hc, fun i ↦ ⟨hc, hcompl i, fun x y hxy ↦ ?_, fun y ↦ ?_⟩⟩,
    fun ⟨hc, h⟩ ↦ ⟨hc, fun i ↦ (h i).2.1, fun x y hxy ↦ Subtype.ext (funext fun i ↦ ?_),
      fun y ↦ ?_⟩⟩
  · have hEq : P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨Pi.single i x.1, hrange ▸ single_mem_pi_univ _ i x.2⟩ =
        P.restrict (fun _ hx ↦ P.mapsTo_range_pow c hx)
        ⟨Pi.single i y.1, hrange ▸ single_mem_pi_univ _ i y.2⟩ := Subtype.ext <| funext fun j ↦ by
      rcases eq_or_ne j i with rfl | hji
      · simpa [P] using congrArg Subtype.val hxy
      · simp [P, hji]
    exact Subtype.ext (by simpa using congrFun (congrArg Subtype.val (hbij.1 hEq)) i)
  · obtain ⟨z, hz⟩ := hbij.2 ⟨Pi.single i y.1, hrange ▸ single_mem_pi_univ _ i y.2⟩
    exact ⟨⟨z.1 i, (hmem z.1).mp z.2 i⟩,
      Subtype.ext (by simpa [P] using congrFun (congrArg Subtype.val hz) i)⟩
  · let a : ↥(LinearMap.range ((T i) ^ c)) := ⟨x.1 i, (hmem x.1).mp x.2 i⟩
    let b : ↥(LinearMap.range ((T i) ^ c)) := ⟨y.1 i, (hmem y.1).mp y.2 i⟩
    have hab : (T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx) a =
        (T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx) b :=
      Subtype.ext (congrFun (congrArg Subtype.val hxy) i)
    exact congrArg Subtype.val ((h i).2.2.1 hab)
  · choose z hz using fun i ↦ (h i).2.2.2 ⟨y.1 i, (hmem y.1).mp y.2 i⟩
    exact ⟨⟨fun i ↦ (z i).1, (hmem _).mpr fun i ↦ (z i).2⟩,
      Subtype.ext (funext fun i ↦ congrArg Subtype.val (hz i))⟩

theorem IsStableAt.piMap {T : ∀ i, End R (M i)} {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ i, (T i).IsStableAt c) :
    IsStableAt (LinearMap.piMap T) c :=
  isStableAt_piMap_iff.mpr ⟨hc, h⟩

@[simp]
theorem lmap_pow (T : ∀ i, End R (M i)) (n : ℕ) :
    (DirectSum.lmap T : End R (⨁ i, M i)) ^ n = DirectSum.lmap fun i ↦ (T i) ^ n := by
  induction n with
  | zero => exact DirectSum.lmap_id.symm
  | succ n ih => rw [pow_succ, mul_eq_comp, ih, ← DirectSum.lmap_comp]; rfl

private theorem lof_mem_comap_pi_univ [DecidableEq ι] (p : ∀ i, Submodule R (M i)) (i : ι)
    {v : M i} (hv : v ∈ p i) :
    DirectSum.lof R ι M i v ∈
      (Submodule.pi Set.univ p).comap (DirectSum.coeFnLinearMap R) := fun j _ ↦ by
  rw [DirectSum.coeFnLinearMap_apply, DirectSum.lof_eq_of]
  rcases eq_or_ne j i with rfl | hji
  · simpa [DirectSum.of_eq_same] using hv
  · rw [DirectSum.of_eq_of_ne i j v hji]
    exact zero_mem (p j)

private theorem isCompl_comap_coeFnLinearMap_pi_univ_iff {p q : ∀ i, Submodule R (M i)} :
    IsCompl ((Submodule.pi Set.univ p).comap (DirectSum.coeFnLinearMap R))
      ((Submodule.pi Set.univ q).comap (DirectSum.coeFnLinearMap R)) ↔
      ∀ i, IsCompl (p i) (q i) := by
  classical
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, eq_bot_iff, eq_top_iff]
  refine ⟨fun ⟨hdisj, hcod⟩ i ↦ ⟨fun v hv ↦ ?_, fun v _ ↦ ?_⟩,
    fun h ↦ ⟨fun x hx ↦ DFinsupp.ext fun i ↦
      (h i).1 ⟨hx.1 i trivial, hx.2 i trivial⟩, fun x hx_top ↦ ?_⟩⟩
  · have h0 := congrArg (DirectSum.component R ι M i)
      (hdisj ⟨lof_mem_comap_pi_univ p i hv.1, lof_mem_comap_pi_univ q i hv.2⟩)
    simpa using h0
  · obtain ⟨u, hu, w, hw, hEq⟩ :=
      Submodule.mem_sup.mp (hcod (x := DirectSum.lof R ι M i v) Submodule.mem_top)
    have hEq_i := congrArg (DirectSum.component R ι M i) hEq
    exact Submodule.mem_sup.mpr ⟨u i, hu i trivial, w i, hw i trivial,
      by simpa [← DirectSum.apply_eq_component] using hEq_i⟩
  · clear hx_top
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of i v =>
      obtain ⟨u, hu, w, hw, hEq⟩ := Submodule.mem_sup.mp ((h i).2 (x := v) Submodule.mem_top)
      rw [← hEq, map_add, ← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R]
      exact add_mem (Submodule.mem_sup_left (lof_mem_comap_pi_univ p i hu))
        (Submodule.mem_sup_right (lof_mem_comap_pi_univ q i hw))
    | add x y hx hy => exact add_mem hx hy

/-- A direct-sum endomorphism `DirectSum.lmap T` on `⨁ i, M i` is stable at `c` if and only if
`1 ≤ c` and every summand `T i` is stable at `c`. -/
@[simp]
theorem isStableAt_lmap_iff {T : ∀ i, End R (M i)} {c : ℕ} :
    IsStableAt (DirectSum.lmap T) c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c := by
  classical
  let S : End R (⨁ i, M i) := DirectSum.lmap T
  have hmem : ∀ x : ⨁ i, M i, x ∈ LinearMap.range (S ^ c) ↔
      ∀ i, x i ∈ LinearMap.range ((T i) ^ c) := fun x ↦ by
    rw [lmap_pow, DirectSum.range_lmap, Submodule.mem_comap, Submodule.mem_pi]; simp
  have hlof : ∀ (i : ι) {v : M i}, v ∈ LinearMap.range ((T i) ^ c) →
      DirectSum.lof R ι M i v ∈ LinearMap.range (S ^ c) := fun i v hv ↦
    (hmem _).mpr fun j ↦ lof_mem_comap_pi_univ (fun k ↦ LinearMap.range ((T k) ^ c)) i hv j trivial
  have hcompl : IsCompl (LinearMap.ker (S ^ c)) (LinearMap.range (S ^ c)) ↔
      ∀ i, IsCompl (LinearMap.ker ((T i) ^ c)) (LinearMap.range ((T i) ^ c)) := by
    change IsCompl (LinearMap.ker (DirectSum.lmap T ^ c))
      (LinearMap.range (DirectSum.lmap T ^ c)) ↔ _
    rw [lmap_pow, DirectSum.ker_lmap, DirectSum.range_lmap,
      isCompl_comap_coeFnLinearMap_pi_univ_iff]
  change S.IsStableAt c ↔ 1 ≤ c ∧ ∀ i, (T i).IsStableAt c
  rw [isStableAt_iff_isCompl_and_bijective_restrict_range_pow, hcompl]
  simp only [isStableAt_iff_isCompl_and_bijective_restrict_range_pow]
  refine ⟨fun ⟨hc, hcompl, hbij⟩ ↦ ⟨hc, fun i ↦ ⟨hc, hcompl i, fun x y hxy ↦ ?_, fun y ↦ ?_⟩⟩,
    fun ⟨hc, h⟩ ↦ ⟨hc, fun i ↦ (h i).2.1, fun x y hxy ↦ Subtype.ext (DFinsupp.ext fun i ↦ ?_),
      fun y ↦ ?_⟩⟩
  · have hEq : S.restrict (fun _ hx ↦ S.mapsTo_range_pow c hx)
          ⟨DirectSum.lof R ι M i x.1, hlof i x.2⟩ =
        S.restrict (fun _ hx ↦ S.mapsTo_range_pow c hx)
          ⟨DirectSum.lof R ι M i y.1, hlof i y.2⟩ :=
      Subtype.ext <| by
        change DirectSum.lmap T (DirectSum.lof R ι M i x.1) =
          DirectSum.lmap T (DirectSum.lof R ι M i y.1)
        rw [DirectSum.lmap_lof, DirectSum.lmap_lof]
        exact congrArg (DirectSum.lof R ι M i) (congrArg Subtype.val hxy)
    have hinj := congrArg (DirectSum.component R ι M i) (congrArg Subtype.val (hbij.1 hEq))
    exact Subtype.ext (by simpa using hinj)
  · obtain ⟨z, hz⟩ := hbij.2 ⟨DirectSum.lof R ι M i y.1, hlof i y.2⟩
    have hzi := congrArg (DirectSum.component R ι M i) (congrArg Subtype.val hz)
    exact ⟨⟨z.1 i, (hmem z.1).mp z.2 i⟩,
      Subtype.ext (by simpa [S, ← DirectSum.apply_eq_component] using hzi)⟩
  · let a : ↥(LinearMap.range ((T i) ^ c)) := ⟨x.1 i, (hmem x.1).mp x.2 i⟩
    let b : ↥(LinearMap.range ((T i) ^ c)) := ⟨y.1 i, (hmem y.1).mp y.2 i⟩
    have hab : (T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx) a =
        (T i).restrict (fun _ hx ↦ (T i).mapsTo_range_pow c hx) b :=
      Subtype.ext (DFunLike.congr_fun (congrArg Subtype.val hxy) i)
    exact congrArg Subtype.val ((h i).2.2.1 hab)
  · let e := fun i ↦ LinearEquiv.ofBijective _ (h i).2.2
    refine ⟨⟨∑ i ∈ y.1.support,
        DirectSum.lof R ι M i ((e i).symm ⟨y.1 i, (hmem y.1).mp y.2 i⟩).1,
        sum_mem fun i _ ↦ hlof i ((e i).symm ⟨y.1 i, (hmem y.1).mp y.2 i⟩).2⟩, Subtype.ext ?_⟩
    rw [LinearMap.coe_restrict_apply, map_sum]
    conv_rhs => rw [← DirectSum.sum_support_of y.1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change DirectSum.lmap T (DirectSum.lof R ι M i _) = _
    rw [DirectSum.lmap_lof, DirectSum.lof_eq_of]
    exact congrArg (DirectSum.of M i) (congrArg Subtype.val ((e i).apply_symm_apply _))

theorem IsStableAt.lmap {T : ∀ i, End R (M i)} {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ i, (T i).IsStableAt c) :
    IsStableAt (DirectSum.lmap T) c :=
  isStableAt_lmap_iff.mpr ⟨hc, h⟩

end Indexed

end ProdPiDirectSum

end Semiring

section Ring

variable {R M N M₁ M₂ : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup M₁] [AddCommGroup M₂] [Module R M] [Module R N] [Module R M₁] [Module R M₂]

/-- A binary product of endomorphisms over a ring is stable if and only if both factors are
stable. -/
@[simp]
theorem isStable_prodMap_iff {T₁ : End R M₁} {T₂ : End R M₂} :
    IsStable (T₁.prodMap T₂) ↔ T₁.IsStable ∧ T₂.IsStable := by
  rw [isStable_def, isStable_def, isStable_def]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := isStableAt_prodMap_iff.mp hc
    exact ⟨⟨c, h₁⟩, ⟨c, h₂⟩⟩
  · exact ⟨max c₁ c₂, (hc₁.mono (le_max_left _ _)).prodMap (hc₂.mono (le_max_right _ _))⟩

theorem IsStable.prodMap {T₁ : End R M₁} {T₂ : End R M₂}
    (h₁ : T₁.IsStable) (h₂ : T₂.IsStable) :
    IsStable (T₁.prodMap T₂) :=
  isStable_prodMap_iff.mpr ⟨h₁, h₂⟩

private theorem comp_projection_of_map_le {pM qM : Submodule R M} {pN qN : Submodule R N}
    (hMN : IsCompl pM qM) (hNP : IsCompl pN qN) {f : M →ₗ[R] N}
    (hp : pM.map f ≤ pN) (hq : qM.map f ≤ qN) :
    f ∘ₗ pM.projection qM hMN = pN.projection qN hNP ∘ₗ f := by
  ext x
  simp only [LinearMap.comp_apply]
  conv_rhs => rw [← Submodule.projection_add_projection_eq_self hMN x]
  rw [map_add, map_add,
    Submodule.projection_apply_of_mem_left hNP (hp ⟨_, Submodule.projection_apply_mem hMN x, rfl⟩),
    Submodule.projection_apply_of_mem_right hNP
      (hq ⟨_, Submodule.projection_apply_mem hMN.symm x, rfl⟩),
    add_zero]

/-- An equivariant linear map between stable operators commutes with the Fitting projections onto
the nilpotent summands `⨆ k, ker (T ^ k)`. -/
theorem IsStable.comp_projection_iSup_ker_pow {T_M : End R M} {T_N : End R N}
    (hM : T_M.IsStable) (hN : T_N.IsStable) {f : M →ₗ[R] N} (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    f ∘ₗ (⨆ k, LinearMap.ker (T_M ^ k)).projection (⨅ k, LinearMap.range (T_M ^ k))
        hM.isCompl_iSup_ker_pow_iInf_range_pow =
      (⨆ k, LinearMap.ker (T_N ^ k)).projection (⨅ k, LinearMap.range (T_N ^ k))
        hN.isCompl_iSup_ker_pow_iInf_range_pow ∘ₗ f :=
  comp_projection_of_map_le _ _ (map_iSup_ker_pow_le_of_comp_eq hf)
    (map_iInf_range_pow_le_of_comp_eq hf)

/-- An equivariant linear map between stable operators commutes with the Fitting projections onto
the invertible summands `⨅ k, range (T ^ k)`. -/
theorem IsStable.comp_projection_iInf_range_pow {T_M : End R M} {T_N : End R N}
    (hM : T_M.IsStable) (hN : T_N.IsStable) {f : M →ₗ[R] N} (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    f ∘ₗ (⨅ k, LinearMap.range (T_M ^ k)).projection (⨆ k, LinearMap.ker (T_M ^ k))
        hM.isCompl_iSup_ker_pow_iInf_range_pow.symm =
      (⨅ k, LinearMap.range (T_N ^ k)).projection (⨆ k, LinearMap.ker (T_N ^ k))
        hN.isCompl_iSup_ker_pow_iInf_range_pow.symm ∘ₗ f :=
  comp_projection_of_map_le _ _ (map_iInf_range_pow_le_of_comp_eq hf)
    (map_iSup_ker_pow_le_of_comp_eq hf)

theorem mapsTo_ker_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    ∀ x ∈ LinearMap.ker f, T_M x ∈ LinearMap.ker f := fun x hx ↦ by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hf, LinearMap.comp_apply,
    LinearMap.mem_ker.mp hx, map_zero]

/-- If `T_M` and `T_N` are both stable at `c`, the restriction of `T_M` to the kernel of an
intertwiner `f : M →ₗ[R] N` is also stable at `c`. -/
theorem IsStableAt.restrict_ker_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) {c : ℕ} (hM : T_M.IsStableAt c) (hN : T_N.IsStableAt c) :
    IsStableAt (T_M.restrict (mapsTo_ker_of_comp_eq hf)) c := by
  let TK := T_M.restrict (mapsTo_ker_of_comp_eq hf)
  have hrange_ge : ∀ x : ↥(LinearMap.ker f), x.1 ∈ LinearMap.range (T_M ^ c) →
      x ∈ LinearMap.range (TK ^ c) := by
    rintro x ⟨y, hy⟩
    have hyM : y ∈ LinearMap.ker (T_M ^ c) ⊔ LinearMap.range (T_M ^ c) := by
      rw [hM.isCompl_ker_pow_range_pow.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hyM
    have hfv_ker : f v ∈ LinearMap.ker (T_N ^ c) := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
        Module.End.commute_pow_left_of_commute hf.symm c, LinearMap.comp_apply]
      have hTMv : (T_M ^ c) v = x.1 := by
        rw [← hy, map_add, LinearMap.mem_ker.mp hu, zero_add]
      rw [hTMv, LinearMap.mem_ker.mp x.2]
    have hfv0 : f v = 0 := Submodule.disjoint_def.mp hN.isCompl_ker_pow_range_pow.disjoint _
      hfv_ker (map_range_pow_le_of_comp_eq hf c ⟨v, hv, rfl⟩)
    refine ⟨⟨v, LinearMap.mem_ker.mpr hfv0⟩, Subtype.ext ?_⟩
    rw [pow_restrict c, LinearMap.coe_restrict_apply, ← hy, map_add,
      LinearMap.mem_ker.mp hu, zero_add]
  rw [isStableAt_iff_isCompl_ker_pow_range_pow]
  refine ⟨hM.one_le, Submodule.disjoint_def.mpr fun x hxk hxr ↦ ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun x ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hxr
    have hxk' : (T_M ^ c) ((TK ^ c) z).1 = 0 := by
      simpa [TK, pow_restrict c] using congrArg Subtype.val (LinearMap.mem_ker.mp hxk)
    have hzM : ((TK ^ c) z).1 ∈ LinearMap.range (T_M ^ c) :=
      ⟨z.1, by simp [TK, pow_restrict c]⟩
    exact Subtype.ext (Submodule.disjoint_def.mp hM.isCompl_ker_pow_range_pow.disjoint _
      (LinearMap.mem_ker.mpr hxk') hzM)
  · have hxM : x.1 ∈ LinearMap.ker (T_M ^ c) ⊔ LinearMap.range (T_M ^ c) := by
      rw [hM.isCompl_ker_pow_range_pow.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxM
    have hfu_eq : f u = -f v := eq_neg_of_add_eq_zero_left <| by
      rw [← map_add, huv, LinearMap.mem_ker.mp x.2]
    have hfu0 : f u = 0 := Submodule.disjoint_def.mp hN.isCompl_ker_pow_range_pow.disjoint _
      (map_ker_pow_le_of_comp_eq hf c ⟨u, hu, rfl⟩)
      (hfu_eq ▸ neg_mem (map_range_pow_le_of_comp_eq hf c ⟨v, hv, rfl⟩))
    have hfv0 : f v = 0 := neg_inj.mp (by rw [← hfu_eq, hfu0, neg_zero])
    refine ⟨⟨u, LinearMap.mem_ker.mpr hfu0⟩, ⟨v, LinearMap.mem_ker.mpr hfv0⟩, ?_,
      hrange_ge _ hv, Subtype.ext huv⟩
    rw [LinearMap.mem_ker, pow_restrict c]
    exact Subtype.ext (LinearMap.mem_ker.mp hu)

theorem IsStable.restrict_ker_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (hM : T_M.IsStable) (hN : T_N.IsStable) :
    IsStable (T_M.restrict (mapsTo_ker_of_comp_eq hf)) := by
  rw [isStable_def] at hM hN ⊢
  obtain ⟨c₁, hc₁⟩ := hM
  obtain ⟨c₂, hc₂⟩ := hN
  exact ⟨max c₁ c₂, IsStableAt.restrict_ker_of_comp_eq hf
    (hc₁.mono (le_max_left _ _)) (hc₂.mono (le_max_right _ _))⟩

theorem range_le_comap_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    LinearMap.range f ≤ (LinearMap.range f).comap T_N := by
  rintro _ ⟨x, rfl⟩
  exact ⟨T_M x, LinearMap.congr_fun hf x⟩

private theorem ker_mapQ_range_pow_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) {c : ℕ} (hM : T_M.IsStableAt c) (hN : T_N.IsStableAt c) :
    LinearMap.ker
        (((LinearMap.range f).mapQ (LinearMap.range f) T_N (range_le_comap_of_comp_eq hf)) ^ c) =
      (LinearMap.ker (T_N ^ c)).map (LinearMap.range f).mkQ := by
  let Rf := LinearMap.range f
  let TQ := Rf.mapQ Rf T_N (range_le_comap_of_comp_eq hf)
  have hpow : TQ ^ c = Rf.mapQ Rf (T_N ^ c)
      (Rf.le_comap_pow_of_le_comap (range_le_comap_of_comp_eq hf) c) :=
    (Rf.mapQ_pow (range_le_comap_of_comp_eq hf) c).symm
  change LinearMap.ker (TQ ^ c) = (LinearMap.ker (T_N ^ c)).map Rf.mkQ
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Rf z
    have hy : (T_N ^ c) y ∈ Rf := by
      rw [← Submodule.ker_mkQ Rf, LinearMap.mem_ker]
      simpa [TQ, hpow] using LinearMap.mem_ker.mp hz
    obtain ⟨m, hm⟩ := hy
    have hmM : m ∈ LinearMap.ker (T_M ^ c) ⊔ LinearMap.range (T_M ^ c) := by
      rw [hM.isCompl_ker_pow_range_pow.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, _, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hmM
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
      ((LinearMap.range f).mapQ (LinearMap.range f) T_N (range_le_comap_of_comp_eq hf)) c := by
  let Rf := LinearMap.range f
  let TQ := Rf.mapQ Rf T_N (range_le_comap_of_comp_eq hf)
  have hrange : LinearMap.range (TQ ^ c) = (LinearMap.range (T_N ^ c)).map Rf.mkQ := by
    rw [← Rf.mapQ_pow (range_le_comap_of_comp_eq hf) c, Submodule.range_mapQ]
  rw [isStableAt_iff_isCompl_ker_pow_range_pow, ker_mapQ_range_pow_of_comp_eq hf hM hN, hrange]
  refine ⟨hM.one_le, Submodule.disjoint_def.mpr ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ ⟨r, hr, hkr⟩
    have hsub : k - r ∈ Rf := by
      rw [← Submodule.ker_mkQ Rf, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hkr.symm
    obtain ⟨m, hm⟩ := hsub
    have hmM : m ∈ LinearMap.ker (T_M ^ c) ⊔ LinearMap.range (T_M ^ c) := by
      rw [hM.isCompl_ker_pow_range_pow.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hmM
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

theorem IsStable.mapQ_range_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (hM : T_M.IsStable) (hN : T_N.IsStable) :
    IsStable ((LinearMap.range f).mapQ (LinearMap.range f) T_N (range_le_comap_of_comp_eq hf)) := by
  rw [isStable_def] at hM hN ⊢
  obtain ⟨c₁, hc₁⟩ := hM
  obtain ⟨c₂, hc₂⟩ := hN
  exact ⟨max c₁ c₂, IsStableAt.mapQ_range_of_comp_eq hf
    (hc₁.mono (le_max_left _ _)) (hc₂.mono (le_max_right _ _))⟩

end Ring

end Module.End

end
