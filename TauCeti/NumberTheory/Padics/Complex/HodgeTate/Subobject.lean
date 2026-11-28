/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.StdBasis

/-!
# Hodge–Tate jumps of subobjects and jointly injective maps

Given a family of `φ`-semilinear maps `f i : T' → S i` equivariant near `1` and ring maps
`δ i : R →+* ℂ_p` with `δ i ∘ φ = γ'`, if the coordinate vectors of `f i (e a)` on a finite basis
`e` of `T'` are `ℂ_p`-linearly independent, then the pullbacks of any `ℂ_p`-bases of semilinear
forms on the `S i` span all `γ'`-semilinear forms on `T'` (`PadicComplex.top_le_span_pullback`).

Consequently, when each `S i` admits a finite `ℂ_p`-basis of Hodge–Tate maps, every Hodge–Tate
jump of `T'` at `γ'` is a jump of some `S i` at `δ i`
(`PadicComplex.exists_hodgeTateJump_ne_zero_of_linearIndependent`). In particular, for finitely
many jointly injective equivariant `R`-linear maps `f i : T → S i` over an integral domain `R`
faithfully embedded in `ℂ_p`, every jump of `T` is a jump of some `S i`
(`PadicComplex.exists_hodgeTateJump_ne_zero_of_jointly_injective`).

## Main results

* `PadicComplex.top_le_span_pullback`: pullbacks of bases of semilinear forms span all semilinear
  forms on `T'` under coordinate linear independence.
* `PadicComplex.exists_hodgeTateJump_ne_zero_of_linearIndependent`: every jump of `T'` is a jump
  of some `S i`.
* `PadicComplex.exists_hodgeTateJump_ne_zero_of_jointly_injective`: every jump of a subobject
  embedded via finitely many jointly injective equivariant maps is a jump of some target `S i`.

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean`
(`New.Period.top_le_span_pullback`, `New.Period.exists_jump_of_linearIndependent`,
`New.Period.exists_jump_of_jointly_injective`).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime]

/-- Under coordinate linear independence over `ℂ_p`, the pullbacks of any `ℂ_p`-bases of
`δ i`-semilinear forms on `S i` along `f i : T' →ₛₗ[φ] S i` span all `γ'`-semilinear forms on
`T'`. -/
theorem top_le_span_pullback {R R' T' ι κ : Type*} [CommRing R] [CommRing R'] [AddCommGroup T']
    [Module R' T'] [Finite κ] {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    {φ : R' →+* R} {γ' : R' →+* ℂ_[p]} {δ : ι → R →+* ℂ_[p]}
    [∀ i, RingHomCompTriple φ (δ i) γ'] {n m : ι → Type*}
    (e : Basis κ R' T') (eS : ∀ i, Basis (n i) R (S i)) (f : ∀ i, T' →ₛₗ[φ] S i)
    (hindep : LinearIndependent ℂ_[p]
      fun (a : κ) (l : Σ i : ι, n i) ↦ δ l.fst ((eS l.fst).coord l.snd (f l.fst (e a))))
    (b : ∀ i, Basis (m i) ℂ_[p] (S i →ₛₗ[δ i] ℂ_[p])) :
    ⊤ ≤ Submodule.span ℂ_[p]
      (Set.range fun y : Σ i : ι, m i ↦ (b y.fst y.snd).comp (f y.fst)) := by
  classical
  let _ := Fintype.ofFinite κ
  let W : Submodule ℂ_[p] (T' →ₛₗ[γ'] ℂ_[p]) :=
    Submodule.span ℂ_[p] (Set.range fun y : Σ i : ι, m i ↦ (b y.fst y.snd).comp (f y.fst))
  let eval : (T' →ₛₗ[γ'] ℂ_[p]) →ₗ[ℂ_[p]] (κ → ℂ_[p]) :=
    LinearMap.pi fun a ↦ LinearMap.id.flip (e a)
  have hpull (i : ι) (F : S i →ₛₗ[δ i] ℂ_[p]) : F.comp (f i) ∈ W :=
    Submodule.span_induction (fun _ ⟨y, hy⟩ ↦ hy ▸ Submodule.subset_span ⟨⟨i, y⟩, rfl⟩)
      (by simp) (fun _ _ _ _ h₁ h₂ ↦ by simpa [LinearMap.add_comp] using add_mem h₁ h₂)
      (fun c _ _ h ↦ by simpa [LinearMap.smul_comp] using Submodule.smul_mem W c h)
      ((b i).mem_span F)
  let v : (Σ i : ι, n i) → (κ → ℂ_[p]) :=
    fun l a ↦ δ l.fst ((eS l.fst).coord l.snd (f l.fst (e a)))
  suffices hspan : Submodule.span ℂ_[p] (Set.range v) = ⊤ from
    (Submodule.map_le_map_iff_of_injective (f := eval) (fun _ _ h ↦ e.ext (congrFun h)) ⊤ W).mp
      (le_top.trans (hspan ▸ Submodule.span_le.mpr (Set.range_subset_iff.mpr fun l ↦
        ⟨((δ l.fst).toSemilinearMap.comp ((eS l.fst).coord l.snd)).comp (f l.fst),
          hpull _ _, rfl⟩)))
  by_contra hne
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span ℂ_[p] (Set.range v))
  have hQne : Q ≠ ⊥ := fun h ↦ hne (by simpa [h] using hQ.sup_eq_top)
  obtain ⟨q, hqQ, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQne
  let bQ := Basis.ofVectorSpace ℂ_[p] Q
  have hrep : bQ.repr ⟨q, hqQ⟩ ≠ 0 := fun h ↦
    hq0 (congrArg Subtype.val (bQ.repr.injective (h.trans (map_zero bQ.repr).symm)))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrep
  let ψ : (κ → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] :=
    (bQ.coord j₀).comp (Submodule.projectionOnto Q _ hQ.symm)
  have hψ_eq (w : κ → ℂ_[p]) : ψ w = ∑ a : κ, w a * ψ (Pi.single a 1) := by
    conv_lhs => rw [show w = ∑ a : κ, w a • Pi.single a (1 : ℂ_[p]) by
      ext a; simp [Finset.sum_apply, Pi.single_apply], map_sum]
    simp [map_smul, smul_eq_mul]
  have hc : ∀ a : κ, ψ (Pi.single a 1) = 0 := Fintype.linearIndependent_iff.mp hindep
    (fun a ↦ ψ (Pi.single a 1)) (funext fun l ↦ by
      have h0 : ψ (v l) = 0 := by
        simp [ψ, Submodule.projectionOnto_apply_right hQ.symm ⟨v l, Submodule.subset_span ⟨l, rfl⟩⟩]
      rw [hψ_eq] at h0
      simpa [v, Finset.sum_apply, mul_comm] using h0)
  have hψq : ψ q = 0 := by rw [hψ_eq]; simp [hc]
  exact hj₀ (by simpa [ψ, Submodule.projectionOnto_apply_left hQ.symm ⟨q, hqQ⟩] using hψq)

/-- If `f i : T' →ₛₗ[φ] S i` are equivariant near `1` with `ℂ_p`-linearly independent coordinate
vectors on a finite basis of `T'`, and each `S i` has a finite `ℂ_p`-basis of Hodge–Tate maps, then
every Hodge–Tate jump of `T'` at `γ'` is a jump of some `S i` at `δ i`. -/
theorem exists_hodgeTateJump_ne_zero_of_linearIndependent {Γ R R' T' ι κ : Type*} [Monoid Γ]
    [CommRing R] [CommRing R'] [AddCommGroup T'] [Module R' T'] [Finite κ]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {σ : Representation R' Γ T'} {τ : ∀ i, Representation R Γ (S i)}
    {φ : R' →+* R} {γ' : R' →+* ℂ_[p]} {δ : ι → R →+* ℂ_[p]}
    [∀ i, RingHomCompTriple φ (δ i) γ'] {n m : ι → Type*} [∀ i, Finite (m i)]
    (e : Basis κ R' T') (eS : ∀ i, Basis (n i) R (S i)) (f : ∀ i, T' →ₛₗ[φ] S i)
    (hequiv : ∀ i, ∀ᶠ g in comap j (𝓝 1), ∀ x : T', f i (σ g x) = τ i g (f i x))
    (hindep : LinearIndependent ℂ_[p]
      fun (a : κ) (l : Σ i : ι, n i) ↦ δ l.fst ((eS l.fst).coord l.snd (f l.fst (e a))))
    {k : ∀ i, m i → ℤ} (b : ∀ i, Basis (m i) ℂ_[p] (S i →ₛₗ[δ i] ℂ_[p]))
    (hb : ∀ i y, b i y ∈ hodgeTateMaps j (τ i) (δ i) (k i y)) {u : ℤ}
    (hu : hodgeTateJump j σ γ' u ≠ 0) :
    ∃ i : ι, hodgeTateJump j (τ i) (δ i) u ≠ 0 := by
  classical
  by_contra! hzero
  have hne : hodgeTateMaps j σ γ' u ≠ ⊥ := fun hbot ↦
    hu (by rw [hodgeTateJump_def, hbot, finrank_bot])
  obtain ⟨F, hFmem, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpull_mem (y : Σ i : ι, m i) :
      (b y.fst y.snd).comp (f y.fst) ∈ hodgeTateMaps j σ γ' (k y.fst y.snd) :=
    mem_hodgeTateMaps.mpr fun x ↦ by
      filter_upwards [hequiv y.fst, mem_hodgeTateMaps.mp (hb y.fst y.snd) (f y.fst x)] with g hg hbg
      simpa [LinearMap.comp_apply, hg x] using hbg
  have hFspan : F ∈ Submodule.span (PadicAlgCl p)
      ((fun y : Σ i : ι, m i ↦ (b y.fst y.snd).comp (f y.fst)) '' {y | k y.fst y.snd = u}) :=
    mem_span_image_of_mem_hodgeTateMaps hj hpull_mem hFmem
      (top_le_span_pullback e eS f hindep b trivial)
  have hempty : {y : Σ i : ι, m i | k y.fst y.snd = u} = ∅ :=
    Set.eq_empty_of_forall_notMem fun y hy ↦ by
      let _ := Fintype.ofFinite (m y.fst)
      have hcard : (Finset.univ.filter fun l : m y.fst ↦ k y.fst l = u).card = 0 := by
        rw [← hodgeTateJump_eq_card_of_basis hj (b y.fst) (hb y.fst)]
        exact hzero y.fst
      exact Finset.notMem_empty y.snd (Finset.card_eq_zero.mp hcard ▸
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
  rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hFspan
  exact hF0 hFspan

/-- Let `R` be an integral domain faithfully embedded in `ℂ_p`, and let `f i : T →ₗ[R] S i` be
finitely many jointly injective equivariant maps from a finite free `R`-representation `T` to
finite free `R`-representations `S i` admitting finite `ℂ_p`-bases of Hodge–Tate maps. Then every
Hodge–Tate jump of `T` is a jump of some `S i`. -/
theorem exists_hodgeTateJump_ne_zero_of_jointly_injective {Γ R T ι κ : Type*} [Monoid Γ]
    [CommRing R] [IsDomain R] [Algebra R ℂ_[p]] [FaithfulSMul R ℂ_[p]]
    [AddCommGroup T] [Module R T] [Finite ι] [Finite κ]
    {S : ι → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {ρ : Representation R Γ T} {τ : ∀ i, Representation R Γ (S i)}
    {n m : ι → Type*} [∀ i, Finite (n i)] [∀ i, Finite (m i)]
    (e : Basis κ R T) (eS : ∀ i, Basis (n i) R (S i)) (f : ∀ i, T →ₗ[R] S i)
    (hequiv : ∀ i g x, f i (ρ g x) = τ i g (f i x))
    (hinj : ∀ x : T, (∀ i, f i x = 0) → x = 0)
    {k : ∀ i, m i → ℤ} (b : ∀ i, Basis (m i) ℂ_[p] (S i →ₛₗ[algebraMap R ℂ_[p]] ℂ_[p]))
    (hb : ∀ i y, b i y ∈ hodgeTateMaps j (τ i) (algebraMap R ℂ_[p]) (k i y)) {u : ℤ}
    (hu : hodgeTateJump j ρ (algebraMap R ℂ_[p]) u ≠ 0) :
    ∃ i : ι, hodgeTateJump j (τ i) (algebraMap R ℂ_[p]) u ≠ 0 := by
  let coords : T →ₗ[R] (Σ i : ι, n i) → R :=
    { toFun := fun x l ↦ (eS l.fst).coord l.snd (f l.fst x)
      map_add' := fun x y ↦ by ext l; simp
      map_smul' := fun r x ↦ by ext l; simp }
  have hker : LinearMap.ker coords = ⊥ := LinearMap.ker_eq_bot'.mpr fun x hx ↦
    hinj x fun i ↦ (eS i).ext_elem fun l ↦ by simpa [coords] using congrFun hx ⟨i, l⟩
  have hlinR : LinearIndependent R (fun a ↦ coords (e a)) := e.linearIndependent.map' coords hker
  have hindep : LinearIndependent ℂ_[p]
      fun (a : κ) (l : Σ i : ι, n i) ↦
        algebraMap R ℂ_[p] ((eS l.fst).coord l.snd (f l.fst (e a))) :=
    (linearIndependent_algebraMap_comp_iff (R := R) (S := ℂ_[p])
      (v := fun a ↦ coords (e a))).mpr hlinR
  exact exists_hodgeTateJump_ne_zero_of_linearIndependent (φ := RingHom.id R)
    (γ' := algebraMap R ℂ_[p]) (δ := fun _ ↦ algebraMap R ℂ_[p]) hj e eS f
    (fun i ↦ Filter.Eventually.of_forall (hequiv i)) hindep b hb hu

end PadicComplex
