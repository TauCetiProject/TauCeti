/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Pi
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.Lie.Cohomology.Continuous.Basic
public import TauCeti.Algebra.Lie.Cohomology.Map

/-!
# Continuous Chevalley–Eilenberg cochains in all degrees

Let `L` be a Lie algebra carrying a topology and `M` a module of coefficients, regarded as discrete.
A Chevalley–Eilenberg `n`-cochain `ω : L [⋀^Fin n]→ₗ[R] M` is continuous for the discrete topology
on `M` precisely when it is locally constant (`IsLocallyConstant ω`), a condition that requires no
`TopologicalSpace` instance on `M`. Such cochains form an `R`-submodule
`TauCeti.LieModule.Cohomology.continuousCochain R L M n` of `L [⋀^Fin n]→ₗ[R] M` in every degree:
sums and scalar multiples of locally constant maps remain locally constant, every `0`-cochain is
continuous (`continuousCochain_zero`), continuous cochains are determined by their values on tuples
drawn from a dense subset of `L` (`continuousCochain_ext_on`), and pulling back along a continuous
Lie algebra morphism while pushing forward along a linear map of coefficients preserves continuity
(`cochainMap_mem_continuousCochain`, `continuousCochainMap`).

When the underlying additive group of `L` is topological, multilinearity and alternation reduce
local constancy everywhere on `Fin (n + 1) → L` to an inductive condition at zero
(`mem_continuousCochain_succ_iff`): `ω` is continuous if and only if every interior product
`ω.curryLeft x` is a continuous `n`-cochain and `ω` vanishes on a neighbourhood of zero in
`Fin (n + 1) → L`. Indeed, expanding `ω (v + z)` over subsets of the coordinates splits off the
all-`v` term `ω v`, the all-`z` term `ω z` (which vanishes near zero), and mixed terms containing at
least one coordinate of `v` and one coordinate of `z`; pulling a `v`-coordinate to the front via
alternation expresses each mixed term through `ω.curryLeft (v i)` near a tuple with a zero entry.
For a basis of neighbourhoods of zero in `L`, this becomes vanishing on a single basic cube
(`mem_continuousCochain_succ_iff_of_hasBasis`), and in degrees one and two it identifies
`continuousCochain` linearly with `continuousOneCochain` and `continuousTwoCochain`
(`continuousCochainOneEquiv`, `continuousCochainTwoEquiv`).

## Main definitions

* `TauCeti.LieModule.Cohomology.continuousCochain`: the submodule of locally constant alternating
  `n`-cochains `L [⋀^Fin n]→ₗ[R] M`.
* `TauCeti.LieModule.Cohomology.continuousCochainMap`,
  `TauCeti.LieModule.Cohomology.continuousCochainEquiv`: functoriality of continuous `n`-cochains
  along continuous Lie morphisms and linear maps of coefficients.
* `TauCeti.LieModule.Cohomology.continuousCochainOneEquiv`,
  `TauCeti.LieModule.Cohomology.continuousCochainTwoEquiv`: linear equivalences with
  `continuousOneCochain` and `continuousTwoCochain` in degrees one and two.

## Main results

* `TauCeti.LieModule.Cohomology.mem_continuousCochain_iff_continuous`: equivalence with continuity
  for any discrete topology on `M`.
* `TauCeti.LieModule.Cohomology.continuousCochain_ext_on`: continuous `n`-cochains agreeing on a
  dense subset of `L` are equal.
* `TauCeti.LieModule.Cohomology.mem_continuousCochain_succ_iff`: inductive characterization of
  continuous `(n + 1)`-cochains via interior products and vanishing near zero.
* `TauCeti.LieModule.Cohomology.mem_continuousCochain_succ_iff_of_hasBasis`: criterion in terms of
  a basis of neighbourhoods of zero in `L`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.
-/

public section

open AlternatingMap Filter Topology _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

section General

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M]

/-- Continuous Chevalley–Eilenberg `n`-cochains with discrete coefficients: the alternating maps
`L [⋀^Fin n]→ₗ[R] M` that are locally constant on `Fin n → L`. -/
def continuousCochain (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier := {ω | IsLocallyConstant ω}
  add_mem' hω hη := hω.add hη
  zero_mem' := IsLocallyConstant.zero
  smul_mem' c _ hω := hω.comp (c • ·)

/-- Every `0`-cochain is continuous, since `Fin 0 → L` is a subsingleton. -/
@[simp]
theorem continuousCochain_zero : continuousCochain R L M 0 = ⊤ :=
  eq_top_iff.mpr fun ω _ ↦ IsLocallyConstant.of_constant ω fun v w ↦
    congrArg ω (Subsingleton.elim v w)

variable {R L M}

theorem mem_continuousCochain_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ continuousCochain R L M n ↔ IsLocallyConstant ω :=
  Iff.rfl

theorem mem_continuousCochain_iff_eventually_eq {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ continuousCochain R L M n ↔ ∀ v : Fin n → L, ∀ᶠ w in 𝓝 v, ω w = ω v :=
  IsLocallyConstant.iff_eventually_eq ω

/-- Every `0`-cochain lies in `continuousCochain R L M 0`. -/
theorem mem_continuousCochain_zero (ω : L [⋀^Fin 0]→ₗ[R] M) :
    ω ∈ continuousCochain R L M 0 := by
  simp [continuousCochain_zero]

/-- An `n`-cochain belongs to `continuousCochain` if and only if it is continuous for a discrete
topology on the coefficients. -/
theorem mem_continuousCochain_iff_continuous [TopologicalSpace M] [DiscreteTopology M] {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ continuousCochain R L M n ↔ Continuous ω :=
  IsLocallyConstant.iff_continuous ω

/-- **Continuous cochains are determined on a dense subset.** Two continuous `n`-cochains agreeing
whenever all arguments belong to a dense subset of `L` are equal. -/
theorem continuousCochain_ext_on {n : ℕ} {ω η : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M n) (hη : η ∈ continuousCochain R L M n) {s : Set L}
    (hs : Dense s) (h : ∀ v : Fin n → L, (∀ i, v i ∈ s) → ω v = η v) : ω = η := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hd : Dense (Set.univ.pi fun _ : Fin n ↦ s) := dense_pi Set.univ fun _ _ ↦ hs
  have hωη := hω.continuous.ext_on hd hη.continuous fun v hv ↦ h v fun i ↦ hv i trivial
  exact AlternatingMap.ext (congrFun hωη)

/-- Inserting a fixed first argument into a continuous `(n + 1)`-cochain yields a continuous
`n`-cochain. -/
theorem curryLeft_mem_continuousCochain {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M (n + 1)) (x : L) :
    ω.curryLeft x ∈ continuousCochain R L M n := by
  have hc : Continuous (fun v : Fin n → L ↦ Matrix.vecCons x v) :=
    continuous_pi <| Fin.cases continuous_const fun i ↦ continuous_apply i
  exact hω.comp_continuous hc

/-- A continuous `(n + 1)`-cochain vanishes on a neighbourhood of zero in `Fin (n + 1) → L`. -/
theorem eventually_eq_zero_of_mem_continuousCochain {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M}
    (hω : ω ∈ continuousCochain R L M (n + 1)) :
    ∀ᶠ v in 𝓝 (0 : Fin (n + 1) → L), ω v = 0 := by
  have h0 : ω 0 = 0 := ω.map_coord_zero 0 rfl
  simpa [h0] using hω.eventually_eq 0

end General

section Map

variable {R L L' L'' M M' M'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
  [LieRing L''] [LieAlgebra R L''] [TopologicalSpace L'']
  [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
  [AddCommGroup M''] [Module R M'']

/-- Pulling a continuous `n`-cochain back along a continuous Lie algebra morphism `φ` and pushing
its values forward along a linear map `e` yields a continuous `n`-cochain. -/
theorem cochainMap_mem_continuousCochain (e : M →ₗ[R] M') {φ : L' →ₗ⁅R⁆ L} (hφ : Continuous φ)
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ continuousCochain R L M n) :
    cochainMap e φ n ω ∈ continuousCochain R L' M' n := by
  have hfun : (cochainMap e φ n ω : (Fin n → L') → M') = e ∘ ω ∘ fun v i ↦ φ (v i) :=
    funext (cochainMap_apply e φ ω)
  rw [mem_continuousCochain_iff, hfun]
  exact (hω.comp_continuous (continuous_pi fun i ↦ hφ.comp (continuous_apply i))).comp e

/-- Pullback along a continuous Lie algebra morphism `φ` and coefficient pushforward along `e`,
restricted to continuous `n`-cochains. -/
def continuousCochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ) (n : ℕ) :
    continuousCochain R L M n →ₗ[R] continuousCochain R L' M' n :=
  (cochainMap e φ n).restrict fun _ hω ↦ cochainMap_mem_continuousCochain e hφ hω

@[simp]
theorem coe_continuousCochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ) {n : ℕ}
    (ω : continuousCochain R L M n) :
    (continuousCochainMap e φ hφ n ω : L' [⋀^Fin n]→ₗ[R] M') = cochainMap e φ n ω :=
  (rfl)

@[simp]
theorem continuousCochainMap_id {hφ : Continuous (LieHom.id : L →ₗ⁅R⁆ L)} (n : ℕ) :
    continuousCochainMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) hφ n =
      LinearMap.id := by
  ext ω : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (cochainMap_id n) ω.1

theorem continuousCochainMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L') (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    (continuousCochainMap e' ψ hψ n).comp (continuousCochainMap e φ hφ n) =
      continuousCochainMap (e'.comp e) (φ.comp ψ) (hφ.comp hψ) n := by
  ext ω : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (cochainMap_comp e e' φ ψ n) ω.1

/-- Transport of continuous `n`-cochains along a bicontinuous Lie equivalence and a linear
equivalence of coefficients. -/
def continuousCochainEquiv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    continuousCochain R L M n ≃ₗ[R] continuousCochain R L' M' n :=
  LinearEquiv.ofLinearMap (continuousCochainMap e.toLinearMap φ.toLieHom hφ n)
    (continuousCochainMap e.symm.toLinearMap φ.symm.toLieHom hφ' n)
    (by
      have hp : φ.symm.toLieHom.comp φ.toLieHom = LieHom.id := by ext; simp
      simpa [e.comp_symm, hp] using
        continuousCochainMap_comp e.symm.toLinearMap e.toLinearMap
          φ.symm.toLieHom φ.toLieHom hφ' hφ n)
    (by
      have hp : φ.toLieHom.comp φ.symm.toLieHom = LieHom.id := by ext; simp
      simpa [e.symm_comp, hp] using
        continuousCochainMap_comp e.toLinearMap e.symm.toLinearMap
          φ.toLieHom φ.symm.toLieHom hφ hφ' n)

@[simp]
theorem continuousCochainEquiv_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    (continuousCochainEquiv e φ hφ hφ' n).toLinearMap =
      continuousCochainMap e.toLinearMap φ.toLieHom hφ n :=
  (rfl)

@[simp]
theorem continuousCochainEquiv_symm_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (n : ℕ) :
    (continuousCochainEquiv e φ hφ hφ' n).symm.toLinearMap =
      continuousCochainMap e.symm.toLinearMap φ.symm.toLieHom hφ' n :=
  (rfl)

@[simp]
theorem continuousCochainEquiv_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) {n : ℕ} (ω : continuousCochain R L M n) :
    continuousCochainEquiv e φ hφ hφ' n ω =
      continuousCochainMap e.toLinearMap φ.toLieHom hφ n ω :=
  (rfl)

@[simp]
theorem continuousCochainEquiv_symm_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) {n : ℕ} (ω : continuousCochain R L' M' n) :
    (continuousCochainEquiv e φ hφ hφ' n).symm ω =
      continuousCochainMap e.symm.toLinearMap φ.symm.toLieHom hφ' n ω :=
  (rfl)

end Map

section TopologicalAddGroup

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [AddCommGroup M] [Module R M]

omit [IsTopologicalAddGroup L] in
/-- Auxiliary lemma for `mem_continuousCochain_succ_iff`: on a proper subset `s` of the slots, the
piecewise tuple `s.piecewise v z` is killed by `ω` for `z` sufficiently close to zero whenever all
interior products of `ω` are locally constant and `ω` vanishes near zero. -/
private theorem eventually_piecewise_eq_zero {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M}
    (hcurry : ∀ x : L, ω.curryLeft x ∈ continuousCochain R L M n)
    (h₀ : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → L), ω z = 0)
    (v : Fin (n + 1) → L) {s : Finset (Fin (n + 1))} (hs : s ≠ Finset.univ) :
    ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → L), ω (s.piecewise v z) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simpa using h₀
  · obtain ⟨j, hj⟩ := not_forall.1 (mt Finset.eq_univ_of_forall hs)
    let g : (Fin (n + 1) → L) → (Fin n → L) :=
      fun z k ↦ (s.piecewise v z) (Equiv.swap 0 i k.succ)
    have hg : Continuous g := by
      refine continuous_pi fun k ↦ ?_
      by_cases hk : Equiv.swap 0 i k.succ ∈ s
      · simp only [g, Finset.piecewise_eq_of_mem _ _ _ hk]
        exact continuous_const
      · simp only [g, Finset.piecewise_eq_of_notMem _ _ _ hk]
        exact continuous_apply _
    have hcons (z : Fin (n + 1) → L) :
        Matrix.vecCons (v i) (g z) = s.piecewise v z ∘ Equiv.swap 0 i := by
      ext k
      refine Fin.cases ?_ (fun _ ↦ rfl) k
      rw [Matrix.cons_val_zero, Function.comp_apply, Equiv.swap_apply_left,
        Finset.piecewise_eq_of_mem _ _ _ hi]
    have hg0 : ω.curryLeft (v i) (g 0) = 0 := by
      rw [curryLeft_apply_apply, hcons 0]
      refine ω.map_coord_zero (Equiv.swap 0 i j) ?_
      rw [Function.comp_apply, Equiv.swap_apply_self, Finset.piecewise_eq_of_notMem _ _ _ hj,
        Pi.zero_apply]
    have hev := (hg.tendsto 0).eventually ((hcurry (v i)).eventually_eq (g 0))
    refine hev.mono fun z hz ↦ ?_
    have hswap : ω (s.piecewise v z ∘ Equiv.swap 0 i) = 0 := by
      rw [← hcons z, ← curryLeft_apply_apply, hz, hg0]
    rcases eq_or_ne i 0 with rfl | hi0
    · simpa using hswap
    · have h := ω.map_swap (s.piecewise v z) hi0.symm
      rw [hswap] at h
      exact neg_eq_zero.mp h.symm

/-- **Inductive characterization of continuous cochains.** Over a topological additive group `L`, an
`(n + 1)`-cochain `ω` is continuous if and only if every interior product `ω.curryLeft x` is a
continuous `n`-cochain and `ω` vanishes on a neighbourhood of zero in `Fin (n + 1) → L`. -/
theorem mem_continuousCochain_succ_iff {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ continuousCochain R L M (n + 1) ↔
      (∀ x : L, ω.curryLeft x ∈ continuousCochain R L M n) ∧
        ∀ᶠ v in 𝓝 (0 : Fin (n + 1) → L), ω v = 0 := by
  refine ⟨fun hω ↦ ⟨curryLeft_mem_continuousCochain hω,
    eventually_eq_zero_of_mem_continuousCochain hω⟩, ?_⟩
  rintro ⟨hcurry, h₀⟩
  rw [mem_continuousCochain_iff_eventually_eq]
  intro v
  have hsub : Tendsto (fun w : Fin (n + 1) → L ↦ w - v) (𝓝 v) (𝓝 0) := by
    have hc : Continuous (fun w : Fin (n + 1) → L ↦ w - v) :=
      continuous_id.sub continuous_const
    simpa [sub_self] using hc.tendsto v
  have hall : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → L),
      ∀ s ∈ (Finset.univ : Finset (Finset (Fin (n + 1)))).erase Finset.univ,
        ω (s.piecewise v z) = 0 :=
    (eventually_all_finset _).mpr fun s hs ↦
      eventually_piecewise_eq_zero hcurry h₀ v (Finset.ne_of_mem_erase hs)
  refine (hsub.eventually hall).mono fun w hw ↦ ?_
  have hv : v + (w - v) = w := add_sub_cancel v w
  rw [← hv, ω.map_add_univ v (w - v),
    Finset.sum_eq_single Finset.univ
      (fun s _ hs ↦ hw s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩)) (by simp)]
  simp

/-- **Basis criterion for continuous cochains.** Given a basis `s` of neighbourhoods of zero in `L`,
an `(n + 1)`-cochain `ω` is continuous if and only if every interior product `ω.curryLeft x` is
continuous and `ω` vanishes when all arguments lie in a single basic neighbourhood `s i`. -/
theorem mem_continuousCochain_succ_iff_of_hasBasis {ι : Type*} {p : ι → Prop} {s : ι → Set L}
    (h : (𝓝 (0 : L)).HasBasis p s) {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ continuousCochain R L M (n + 1) ↔
      (∀ x : L, ω.curryLeft x ∈ continuousCochain R L M n) ∧
        ∃ i, p i ∧ ∀ v : Fin (n + 1) → L, (∀ k, v k ∈ s i) → ω v = 0 := by
  rw [mem_continuousCochain_succ_iff]
  refine and_congr_right' ⟨fun h₀ ↦ ?_, ?_⟩
  · rw [nhds_pi] at h₀
    obtain ⟨⟨I, i⟩, ⟨-, hi⟩, hI⟩ := h.pi_self.eventually_iff.mp h₀
    exact ⟨i, hi, fun v hv ↦ hI fun k _ ↦ hv k⟩
  · rintro ⟨i, hi, hω⟩
    rw [nhds_pi]
    exact (eventually_pi fun _ ↦ h.mem_of_mem hi).mono hω

/-- A `1`-cochain on a topological additive group `L` is continuous if and only if `x ↦ ω ![x]`
vanishes on a neighbourhood of zero in `L`. -/
theorem mem_continuousCochain_one_iff {ω : L [⋀^Fin 1]→ₗ[R] M} :
    ω ∈ continuousCochain R L M 1 ↔ ∀ᶠ x in 𝓝 (0 : L), ω ![x] = 0 := by
  rw [mem_continuousCochain_succ_iff]
  simp only [mem_continuousCochain_zero, implies_true, true_and]
  constructor
  · intro h
    have hc : Continuous (fun x : L ↦ (![x] : Fin 1 → L)) :=
      continuous_pi <| Fin.cases continuous_id fun i ↦ i.elim0
    have h0 : (![(0 : L)] : Fin 1 → L) = 0 := by ext i; exact Fin.cases rfl (fun j ↦ j.elim0) i
    exact (by simpa [h0] using hc.tendsto 0 : Tendsto (fun x : L ↦ ![x]) (𝓝 0) (𝓝 0)).eventually h
  · intro h
    have heq : ∀ v : Fin 1 → L, ![v 0] = v := fun v ↦ by
      ext i; exact Fin.cases rfl (fun j ↦ j.elim0) i
    simpa [heq] using ((continuous_apply 0).tendsto (0 : Fin 1 → L)).eventually h

/-- `oneCochainEquiv` maps `continuousCochain R L M 1` onto `continuousOneCochain R L M`. -/
@[simp]
theorem oneCochainEquiv_mem_continuousOneCochain_iff {ω : L [⋀^Fin 1]→ₗ[R] M} :
    oneCochainEquiv R L M ω ∈ continuousOneCochain R L M ↔
      ω ∈ continuousCochain R L M 1 := by
  simp [mem_continuousOneCochain_iff, mem_continuousCochain_one_iff]

/-- `twoCochainEquiv` maps `continuousCochain R L M 2` onto `continuousTwoCochain R L M`. -/
@[simp]
theorem twoCochainEquiv_mem_continuousTwoCochain_iff {ω : L [⋀^Fin 2]→ₗ[R] M} :
    twoCochainEquiv R L M ω ∈ continuousTwoCochain R L M ↔
      ω ∈ continuousCochain R L M 2 := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  rw [mem_continuousTwoCochain_iff_continuous, mem_continuousCochain_iff_continuous]
  let e : L × L ≃ₜ (Fin 2 → L) :=
    (Homeomorph.finTwoArrow (X := L)).symm
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have heq : (ω : (Fin 2 → L) → M) =
        (fun p : L × L ↦ twoCochainEquiv R L M ω p.1 p.2) ∘ e.symm := by
      ext v
      simp only [Function.comp_apply, e, Homeomorph.symm_symm, Homeomorph.finTwoArrow_apply,
        twoCochainEquiv_apply]
      exact congrArg ω (funext <| Fin.cases rfl fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j)
    rw [heq]
    exact hc.comp e.symm.continuous
  · have heq : (fun p : L × L ↦ twoCochainEquiv R L M ω p.1 p.2) = ω ∘ e := by
      ext ⟨x, y⟩
      simp [e]
    rw [heq]
    exact hc.comp e.continuous

variable (R L M)

/-- Continuous `1`-cochains are linearly equivalent to `continuousOneCochain`. -/
def continuousCochainOneEquiv :
    continuousCochain R L M 1 ≃ₗ[R] continuousOneCochain R L M :=
  LinearEquiv.ofLinearMap
    ((oneCochainEquiv R L M).toLinearMap.restrict fun _ hω ↦
      oneCochainEquiv_mem_continuousOneCochain_iff.mpr hω)
    ((oneCochainEquiv R L M).symm.toLinearMap.restrict fun f hf ↦ by
      rw [← oneCochainEquiv_mem_continuousOneCochain_iff]
      simpa using hf)
    (by ext f; simp)
    (by ext ω; simp)

/-- Continuous `2`-cochains are linearly equivalent to `continuousTwoCochain`. -/
def continuousCochainTwoEquiv :
    continuousCochain R L M 2 ≃ₗ[R] continuousTwoCochain R L M :=
  LinearEquiv.ofLinearMap
    ((twoCochainEquiv R L M).toLinearMap.restrict fun _ hω ↦
      twoCochainEquiv_mem_continuousTwoCochain_iff.mpr hω)
    ((twoCochainEquiv R L M).symm.toLinearMap.restrict fun c hc ↦ by
      rw [← twoCochainEquiv_mem_continuousTwoCochain_iff]
      simpa using hc)
    (by ext c; simp)
    (by ext ω; simp)

variable {R L M}

@[simp]
theorem coe_continuousCochainOneEquiv (ω : continuousCochain R L M 1) :
    (continuousCochainOneEquiv R L M ω : oneCochain R L M) = oneCochainEquiv R L M ω :=
  (rfl)

@[simp]
theorem coe_continuousCochainOneEquiv_symm (f : continuousOneCochain R L M) :
    ((continuousCochainOneEquiv R L M).symm f : L [⋀^Fin 1]→ₗ[R] M) =
      (oneCochainEquiv R L M).symm f :=
  (rfl)

@[simp]
theorem coe_continuousCochainTwoEquiv (ω : continuousCochain R L M 2) :
    (continuousCochainTwoEquiv R L M ω : twoCochain R L M) = twoCochainEquiv R L M ω :=
  (rfl)

@[simp]
theorem coe_continuousCochainTwoEquiv_symm (c : continuousTwoCochain R L M) :
    ((continuousCochainTwoEquiv R L M).symm c : L [⋀^Fin 2]→ₗ[R] M) =
      (twoCochainEquiv R L M).symm c :=
  (rfl)

end TopologicalAddGroup

end TauCeti.LieModule.Cohomology
