/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CentralExtension
public import TauCeti.Algebra.Lie.Current.Coefficient

/-!
# Smooth actions of polynomial and formal currents

An action `ρ` of the polynomial loop algebra `L[t, t⁻¹]` on a module `M` is *smooth* if every
vector `m` is killed by all modes `t^n ⊗ x` with `n` large enough, depending on `m`
(`TauCeti.CurrentAlgebra.IsLoopSmooth`). An action `σ` of the formal currents
`L((t)) = R⸨X⸩ ⊗[R] L` is *smooth* if every vector is killed by the currents of some order
`orderSubmodule R L N` (`TauCeti.CurrentAlgebra.IsSmooth`). Since the order submodules decrease,
`N` may always be taken positive.

A smooth action of polynomial currents extends uniquely to a smooth action of formal currents
(`TauCeti.CurrentAlgebra.extendAction`): a formal current `u` acts on `m` through its polynomial
truncation `trunc R L N u` for any cutoff `N` of `m`, and the result does not depend on the
cutoff. Conversely, a smooth action of formal currents restricts along `ofLoop` to a smooth action
of polynomial currents, and it is the extension of its restriction. Extension preserves
commutators: the composite of the actions of `u` and `v` on `m` is computed by truncating both at
a common cutoff, chosen large in terms of `m`, of the vector `v • m`, and of the lower orders of
`u` and `v`. Hence the extension of a representation is a representation. Linear maps
intertwining two smooth actions of polynomial currents intertwine their extensions.

The same holds for the residue central extensions `L[t, t⁻¹] ⊕ R K` and `L((t)) ⊕ R K` of an
invariant symmetric form `Φ`, embedded in each other by `ofLoopExtension`, with smoothness imposed
on the currents `(u, 0)`. The extended action (`TauCeti.CurrentAlgebra.extendExtensionAction`)
lets central elements act as before, so in particular `K` acts by the same operator. Here the
commutator of truncations also produces the residue cocycle of the truncations, which agrees with
the residue cocycle of the formal currents once the cutoff exceeds minus their lower orders.

For representations this gives the bijections `TauCeti.CurrentAlgebra.smoothLieHomEquiv` and
`TauCeti.CurrentAlgebra.smoothExtensionLieHomEquiv`, by extension and restriction, compatible with
intertwiners. Only finite sums of modes act on each vector, so no completeness of `M` or of the
currents is used, and `L` is an arbitrary Lie algebra over a commutative ring, which for the
residue extensions is additively torsion-free, as Mathlib's polynomial residue cocycle requires.

The actions are linear maps into `Module.End R M`; representations are Lie algebra morphisms into
`Module.End R M` with its commutator bracket `LieRing.ofAssociativeRing`.

## Main definitions

* `TauCeti.CurrentAlgebra.IsLoopSmooth`, `TauCeti.CurrentAlgebra.IsSmooth`: smoothness of actions
  of polynomial and of formal currents.
* `TauCeti.CurrentAlgebra.extendAction`, `TauCeti.CurrentAlgebra.extendLieHom`: the extension of a
  smooth polynomial action or representation.
* `TauCeti.CurrentAlgebra.extendExtensionAction`, `TauCeti.CurrentAlgebra.extendExtensionLieHom`:
  the same for the residue central extensions.
* `TauCeti.CurrentAlgebra.smoothLieHomEquiv`, `TauCeti.CurrentAlgebra.smoothExtensionLieHomEquiv`:
  smooth representations of polynomial and of formal currents, or of their residue central
  extensions, correspond by extension and restriction.

## Main results

* `TauCeti.CurrentAlgebra.eventually_apply_trunc_eq`: the extension acts through truncation at all
  large cutoffs.
* `TauCeti.CurrentAlgebra.eq_extendAction_iff`,
  `TauCeti.CurrentAlgebra.eq_extendExtensionAction_iff`: a smooth action is the extension of a
  polynomial action exactly when it restricts to it.
* `TauCeti.CurrentAlgebra.extendAction_lie`, `TauCeti.CurrentAlgebra.extendExtensionAction_lie`:
  extension preserves commutators.
* `TauCeti.CurrentAlgebra.forall_comp_extendAction_eq_iff`,
  `TauCeti.CurrentAlgebra.forall_comp_extendExtensionAction_eq_iff`: a linear map intertwines two
  extensions exactly when it intertwines the polynomial actions.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3 and §2.1, for smooth modules over
  loop algebras and their affine central extensions, and the extension of polynomial actions by
  finite truncation.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open Filter

namespace TauCeti.CurrentAlgebra

variable {R L M M' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

local notation "P" => LieAlgebra.loopAlgebra R ℤ L
local notation "C" => currentAlgebra R L

section Smooth

/-- An action of polynomial currents is smooth if every vector is killed by all modes
`t^n ⊗ x` with `n` at least a cutoff depending on the vector. -/
def IsLoopSmooth (ρ : P →ₗ[R] Module.End R M) : Prop :=
  ∀ m : M, ∃ N : ℤ, ∀ n, N ≤ n → ∀ x : L, ρ (AddMonoidAlgebra.single n 1 ⊗ₜ x) m = 0

/-- An action of formal currents is smooth if every vector is killed by all currents of order
at least a cutoff depending on the vector. -/
def IsSmooth (σ : C →ₗ[R] Module.End R M) : Prop :=
  ∀ m : M, ∃ N : ℤ, ∀ u ∈ orderSubmodule R L N, σ u m = 0

variable {ρ : LieAlgebra.loopAlgebra R ℤ L →ₗ[R] Module.End R M}

/-- If all modes of order at least `N` kill `m`, then so does every polynomial current of order at
least `N`. -/
theorem apply_apply_eq_zero_of_ofLoop_mem_orderSubmodule {N : ℤ} {m : M}
    (hN : ∀ n, N ≤ n → ∀ x : L, ρ (AddMonoidAlgebra.single n 1 ⊗ₜ x) m = 0) {p : P}
    (hp : ofLoop R L p ∈ orderSubmodule R L N) : ρ p m = 0 := by
  have h := apply_trunc_ofLoop R L (ρ.flip m) (by simpa using hN) p
  rw [trunc_eq_zero_of_mem_orderSubmodule R L hp, map_zero] at h
  simpa using h.symm

/-- Smoothness of a polynomial action, stated with the order submodules of formal currents. -/
theorem isLoopSmooth_iff :
    IsLoopSmooth ρ ↔ ∀ m : M, ∃ N : ℤ, ∀ p : P, ofLoop R L p ∈ orderSubmodule R L N → ρ p m = 0 :=
  ⟨fun hρ m ↦ (hρ m).imp fun _ hN _ ↦ apply_apply_eq_zero_of_ofLoop_mem_orderSubmodule hN,
    fun hρ m ↦ (hρ m).imp fun _ hN n hn x ↦ hN _ <|
      orderSubmodule_antitone R L hn (ofLoop_single_tmul_mem_orderSubmodule R L n x)⟩

/-- A smooth action of formal currents restricts to a smooth action of polynomial currents. -/
theorem IsSmooth.comp_ofLoop {σ : C →ₗ[R] Module.End R M} (hσ : IsSmooth σ) :
    IsLoopSmooth (σ ∘ₗ (ofLoop R L).toLinearMap) :=
  isLoopSmooth_iff.mpr fun m ↦ (hσ m).imp fun _ hN _ hp ↦ hN _ hp

/-- Truncations of a current at two cutoffs of `m` act in the same way on `m`. -/
private theorem apply_trunc_apply_eq {N N' : ℤ} {m : M}
    (hN : ∀ p : P, ofLoop R L p ∈ orderSubmodule R L N → ρ p m = 0) (hNN' : N ≤ N')
    (u : C) : ρ (trunc R L N' u) m = ρ (trunc R L N u) m := by
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub]
  refine hN _ ?_
  have h := Submodule.sub_mem _
    (orderSubmodule_antitone R L hNN' (ofLoop_trunc_sub_mem_orderSubmodule R L N' u))
    (ofLoop_trunc_sub_mem_orderSubmodule R L N u)
  rwa [sub_sub_sub_cancel_right, ← map_sub] at h

end Smooth

section Extend

variable (ρ : LieAlgebra.loopAlgebra R ℤ L →ₗ[R] Module.End R M) (hρ : IsLoopSmooth ρ)

/-- Truncation at the chosen cutoff of `m` acts on `m` as truncation at any other cutoff. -/
private theorem apply_trunc_choose_eq (u : C) {m : M} {N : ℤ}
    (hN : ∀ p : P, ofLoop R L p ∈ orderSubmodule R L N → ρ p m = 0) :
    ρ (trunc R L (isLoopSmooth_iff.mp hρ m).choose u) m = ρ (trunc R L N u) m := by
  rw [← apply_trunc_apply_eq (isLoopSmooth_iff.mp hρ m).choose_spec (le_max_left _ N),
    apply_trunc_apply_eq hN (le_max_right _ N)]

/-- The action of formal currents extending a smooth action of polynomial currents. A current `u`
acts on `m` through its polynomial truncation below a cutoff of `m`; the result does not depend on
the cutoff (`TauCeti.CurrentAlgebra.extendAction_apply_of_forall`). -/
def extendAction : C →ₗ[R] Module.End R M :=
  LinearMap.mk₂ R (fun u m ↦ ρ (trunc R L (isLoopSmooth_iff.mp hρ m).choose u) m)
    (fun u v m ↦ by simp) (fun r u m ↦ by simp)
    (fun u m m' ↦ by
      -- Both summands are killed by currents of order at least the larger of their cutoffs.
      have hm := (isLoopSmooth_iff.mp hρ m).choose_spec
      have hm' := (isLoopSmooth_iff.mp hρ m').choose_spec
      have hle := le_max_left (isLoopSmooth_iff.mp hρ m).choose (isLoopSmooth_iff.mp hρ m').choose
      have hle' :=
        le_max_right (isLoopSmooth_iff.mp hρ m).choose (isLoopSmooth_iff.mp hρ m').choose
      rw [apply_trunc_choose_eq ρ hρ u fun p hp ↦ by
          rw [map_add, hm p (orderSubmodule_antitone R L hle hp),
            hm' p (orderSubmodule_antitone R L hle' hp), add_zero],
        map_add, apply_trunc_apply_eq hm hle, apply_trunc_apply_eq hm' hle'])
    (fun r u m ↦ by
      have hm := (isLoopSmooth_iff.mp hρ m).choose_spec
      rw [apply_trunc_choose_eq ρ hρ u fun p hp ↦ by rw [map_smul, hm p hp, smul_zero], map_smul])

/-- The extension acts on `m` through truncation below any cutoff of `m`. -/
theorem extendAction_apply_of_forall {N : ℤ} {m : M}
    (hN : ∀ n, N ≤ n → ∀ x : L, ρ (AddMonoidAlgebra.single n 1 ⊗ₜ x) m = 0) (u : C) :
    extendAction ρ hρ u m = ρ (trunc R L N u) m := by
  rw [extendAction, LinearMap.mk₂_apply,
    apply_trunc_choose_eq ρ hρ u fun _ ↦ apply_apply_eq_zero_of_ofLoop_mem_orderSubmodule hN]

/-- The extension acts on `m` through truncation at every sufficiently large cutoff. -/
theorem eventually_apply_trunc_eq (u : C) (m : M) :
    ∀ᶠ N in atTop, ρ (trunc R L N u) m = extendAction ρ hρ u m := by
  obtain ⟨N₀, hN₀⟩ := hρ m
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact (extendAction_apply_of_forall ρ hρ (fun n hn ↦ hN₀ n (hN.trans hn)) u).symm

/-- The extension restricts to the given action on polynomial currents. -/
@[simp]
theorem extendAction_ofLoop (p : P) : extendAction ρ hρ (ofLoop R L p) = ρ p := by
  ext m
  obtain ⟨N, hN⟩ := hρ m
  rw [extendAction_apply_of_forall ρ hρ hN]
  exact apply_trunc_ofLoop R L (ρ.flip m) (by simpa using hN) p

/-- The extension restricts to the given action on polynomial currents. -/
@[simp]
theorem extendAction_comp_ofLoop : extendAction ρ hρ ∘ₗ (ofLoop R L).toLinearMap = ρ :=
  LinearMap.ext fun p ↦ extendAction_ofLoop ρ hρ p

/-- The extension of a smooth action is smooth, with the same cutoffs. -/
theorem isSmooth_extendAction : IsSmooth (extendAction ρ hρ) := fun m ↦ by
  obtain ⟨N, hN⟩ := hρ m
  refine ⟨N, fun u hu ↦ ?_⟩
  rw [extendAction_apply_of_forall ρ hρ hN, trunc_eq_zero_of_mem_orderSubmodule R L hu,
    map_zero, LinearMap.zero_apply]

/-- A smooth action of formal currents is the extension of a smooth polynomial action exactly
when it restricts to that action. -/
theorem eq_extendAction_iff {σ : C →ₗ[R] Module.End R M} (hσ : IsSmooth σ) :
    σ = extendAction ρ hρ ↔ σ ∘ₗ (ofLoop R L).toLinearMap = ρ := by
  refine ⟨fun h ↦ h ▸ extendAction_comp_ofLoop ρ hρ,
    fun h ↦ LinearMap.ext fun u ↦ LinearMap.ext fun m ↦ ?_⟩
  obtain ⟨N, hN⟩ := hσ m
  obtain ⟨N', hN'⟩ := hρ m
  -- At a cutoff for both actions, `u` and its truncation act in the same way.
  have hN'' (n : ℤ) (hn : max N N' ≤ n) (x : L) :
      ρ (AddMonoidAlgebra.single n 1 ⊗ₜ x) m = 0 := hN' n ((le_max_right _ _).trans hn) x
  have hu := hN _ (orderSubmodule_antitone R L (le_max_left N N')
    (ofLoop_trunc_sub_mem_orderSubmodule R L (max N N') u))
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hu
  rw [extendAction_apply_of_forall ρ hρ hN'', ← hu, ← h, LinearMap.comp_apply,
    LieHom.coe_toLinearMap]

/-- Smooth actions of formal currents with the same restriction to polynomial currents agree. -/
theorem IsSmooth.ext {σ τ : C →ₗ[R] Module.End R M} (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (h : σ ∘ₗ (ofLoop R L).toLinearMap = τ ∘ₗ (ofLoop R L).toLinearMap) : σ = τ :=
  ((eq_extendAction_iff _ hτ.comp_ofLoop hσ).mpr h).trans
    ((eq_extendAction_iff _ hτ.comp_ofLoop hτ).mpr rfl).symm

/-- The composite of the actions of two currents on `m` is computed by truncating both currents
at every sufficiently large common cutoff. -/
theorem eventually_apply_trunc_apply_trunc_eq (u v : C) (m : M) :
    ∀ᶠ N in atTop, ρ (trunc R L N u) (ρ (trunc R L N v) m) =
      extendAction ρ hρ u (extendAction ρ hρ v m) := by
  filter_upwards [eventually_apply_trunc_eq ρ hρ u (extendAction ρ hρ v m),
    eventually_apply_trunc_eq ρ hρ v m] with N hu hv
  rw [hv, hu]

/-- The bracket of the truncations of two currents acts on `m` as the extension of their bracket,
at every sufficiently large common cutoff. -/
theorem eventually_apply_lie_trunc_eq (u v : C) (m : M) :
    ∀ᶠ N in atTop, ρ ⁅trunc R L N u, trunc R L N v⁆ m = extendAction ρ hρ ⁅u, v⁆ m := by
  obtain ⟨Mu, hu⟩ := exists_mem_orderSubmodule R L u
  obtain ⟨Mv, hv⟩ := exists_mem_orderSubmodule R L v
  obtain ⟨N₀, hN₀⟩ := isLoopSmooth_iff.mp hρ m
  filter_upwards [eventually_apply_trunc_eq ρ hρ ⁅u, v⁆ m, eventually_ge_atTop (N₀ - Mu),
    eventually_ge_atTop (N₀ - Mv), eventually_ge_atTop N₀] with N huvN hNu hNv hN
  rw [← huvN, ← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub]
  -- Both polynomial currents agree with `⁅u, v⁆` up to currents of order at least `N₀`.
  refine hN₀ _ ?_
  have h := Submodule.sub_mem _
    (lie_ofLoop_trunc_sub_mem_orderSubmodule R L hu hv (by omega : N₀ ≤ N + Mv)
      (by omega : N₀ ≤ Mu + N))
    (orderSubmodule_antitone R L hN (ofLoop_trunc_sub_mem_orderSubmodule R L N ⁅u, v⁆))
  rwa [sub_sub_sub_cancel_right, ← LieHom.map_lie, ← map_sub] at h

/-- Extension preserves commutators: if the polynomial action takes brackets to commutators, then
so does its extension. -/
theorem extendAction_lie (hρL : ∀ p q : P, ρ ⁅p, q⁆ = ρ p * ρ q - ρ q * ρ p) (u v : C) :
    extendAction ρ hρ ⁅u, v⁆ =
      extendAction ρ hρ u * extendAction ρ hρ v - extendAction ρ hρ v * extendAction ρ hρ u := by
  ext m
  obtain ⟨N, h, huv, hvu⟩ := (eventually_apply_lie_trunc_eq ρ hρ u v m |>.and <|
    eventually_apply_trunc_apply_trunc_eq ρ hρ u v m |>.and <|
    eventually_apply_trunc_apply_trunc_eq ρ hρ v u m).exists
  rw [← h, hρL, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, huv, hvu]

/-- A linear map intertwines the extensions of two smooth polynomial actions exactly when it
intertwines the polynomial actions. -/
theorem forall_comp_extendAction_eq_iff {ρ' : P →ₗ[R] Module.End R M'} (hρ' : IsLoopSmooth ρ')
    (f : M →ₗ[R] M') :
    (∀ u : C, f ∘ₗ extendAction ρ hρ u = extendAction ρ' hρ' u ∘ₗ f) ↔
      ∀ p : P, f ∘ₗ ρ p = ρ' p ∘ₗ f := by
  refine ⟨fun h p ↦ by simpa using h (ofLoop R L p), fun h u ↦ LinearMap.ext fun m ↦ ?_⟩
  obtain ⟨N, hN, hN'⟩ := (eventually_apply_trunc_eq ρ hρ u m |>.and <|
    eventually_apply_trunc_eq ρ' hρ' u (f m)).exists
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hN, ← hN', ← LinearMap.comp_apply, h,
    LinearMap.comp_apply]

end Extend

section LieHom

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation of formal currents extending a smooth representation of polynomial
currents. -/
def extendLieHom (ρ : P →ₗ⁅R⁆ Module.End R M) (hρ : IsLoopSmooth ρ.toLinearMap) :
    C →ₗ⁅R⁆ Module.End R M where
  __ := extendAction ρ.toLinearMap hρ
  map_lie' {u v} := (extendAction_lie ρ.toLinearMap hρ (fun p q ↦ by
    simp [LieRing.of_associative_ring_bracket]) u v).trans
      (LieRing.of_associative_ring_bracket _ _).symm

/-- The extended representation is the extended action. -/
@[simp]
theorem toLinearMap_extendLieHom (ρ : P →ₗ⁅R⁆ Module.End R M)
    (hρ : IsLoopSmooth ρ.toLinearMap) :
    (extendLieHom ρ hρ).toLinearMap = extendAction ρ.toLinearMap hρ :=
  (rfl)

/-- The extended representation restricts to the given representation of polynomial currents. -/
@[simp]
theorem extendLieHom_comp_ofLoop (ρ : P →ₗ⁅R⁆ Module.End R M)
    (hρ : IsLoopSmooth ρ.toLinearMap) : (extendLieHom ρ hρ).comp (ofLoop R L) = ρ :=
  LieHom.ext fun p ↦ extendAction_ofLoop ρ.toLinearMap hρ p

/-- Smooth representations of polynomial currents correspond to smooth representations of formal
currents, by extension and by restriction along `ofLoop`. -/
def smoothLieHomEquiv :
    {ρ : P →ₗ⁅R⁆ Module.End R M // IsLoopSmooth ρ.toLinearMap} ≃
      {σ : C →ₗ⁅R⁆ Module.End R M // IsSmooth σ.toLinearMap} where
  toFun ρ := ⟨extendLieHom ρ.1 ρ.2, isSmooth_extendAction _ ρ.2⟩
  invFun σ := ⟨σ.1.comp (ofLoop R L), σ.2.comp_ofLoop⟩
  left_inv ρ := Subtype.ext (extendLieHom_comp_ofLoop ρ.1 ρ.2)
  right_inv σ := Subtype.ext <| LieHom.ext fun u ↦ LinearMap.congr_fun
    ((eq_extendAction_iff _ σ.2.comp_ofLoop σ.2).mpr rfl).symm u

/-- The correspondence sends a smooth representation of polynomial currents to its extension. -/
@[simp]
theorem coe_smoothLieHomEquiv_apply
    (ρ : {ρ : P →ₗ⁅R⁆ Module.End R M // IsLoopSmooth ρ.toLinearMap}) :
    (smoothLieHomEquiv ρ : C →ₗ⁅R⁆ Module.End R M) = extendLieHom ρ.1 ρ.2 :=
  (rfl)

/-- The inverse correspondence restricts a smooth representation of formal currents along
`ofLoop`. -/
@[simp]
theorem coe_smoothLieHomEquiv_symm_apply
    (σ : {σ : C →ₗ⁅R⁆ Module.End R M // IsSmooth σ.toLinearMap}) :
    (smoothLieHomEquiv.symm σ : P →ₗ⁅R⁆ Module.End R M) = σ.1.comp (ofLoop R L) :=
  (rfl)

end LieHom

section Extension

open LieAlgebra LieModule.Cohomology

variable [HasUniqueDiv R] {Φ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm}

local notation "cP" => LieAlgebra.LoopAlgebra.twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "cC" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "ZP" => TrivialLieModule R P R
local notation "ZC" => TrivialLieModule R C R
-- The current coordinate sections of the polynomial and formal residue central extensions.
local notation "sP" => LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP
local notation "sC" => LinearEquiv.toLinearMap (ofProdLinearEquiv cC) ∘ₗ LinearMap.inl R C ZC
-- The identification of the centre of the formal extension with that of the polynomial one.
local notation "zP" =>
  LinearEquiv.trans (TrivialLieModule.equiv R C R) (LinearEquiv.symm (TrivialLieModule.equiv R P R))

/-- The action of the residue central extension of formal currents extending an action `ρ` of the
residue central extension of polynomial currents which is smooth on currents. A pair `(u, z)` of
a formal current and a central coordinate acts by the extension of `ρ` on `u`, plus the action of
the central element `(0, z)` under `ρ`. -/
def extendExtensionAction (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) : ofTwoCocycle cC →ₗ[R] Module.End R M :=
  extendAction (ρ ∘ₗ sP) hρ ∘ₗ (ofTwoCocycle.proj cC).toLinearMap +
    ρ ∘ₗ LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inr R P ZP ∘ₗ
      LinearEquiv.toLinearMap zP ∘ₗ LinearMap.snd R C ZC ∘ₗ
        LinearEquiv.toLinearMap (ofProdLinearEquiv cC).symm

/-- The extended action of a pair `(u, z)` of a formal current and a central coordinate. -/
@[simp]
theorem extendExtensionAction_ofProd (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) (u : C) (z : ZC) :
    extendExtensionAction ρ hρ (ofProd cC (u, z)) =
      extendAction (ρ ∘ₗ sP) hρ u + ρ (ofProd cP (0, zP z)) := by
  simp [extendExtensionAction, ofTwoCocycle.proj_apply, coe_ofProdLinearEquiv,
    coe_ofProdLinearEquiv_symm]

/-- On currents, the extended action is the extension of the action on polynomial currents. -/
@[simp]
theorem extendExtensionAction_comp_section (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) :
    extendExtensionAction ρ hρ ∘ₗ sC = extendAction (ρ ∘ₗ sP) hρ := by
  refine LinearMap.ext fun u ↦ ?_
  simp only [extendExtensionAction_ofProd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.inl_apply, coe_ofProdLinearEquiv, map_zero, Prod.mk_zero_zero, of_zero, add_zero]

/-- The extended action restricts to the given action along the embedding of the polynomial
residue central extension. -/
@[simp]
theorem extendExtensionAction_ofLoopExtension (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) (x : ofTwoCocycle cP) :
    extendExtensionAction ρ hρ (ofLoopExtension Φ hΦ hΦs x) = ρ x := by
  obtain ⟨⟨p, z⟩, rfl⟩ := (ofProd cP).surjective x
  have h := extendAction_ofLoop (ρ ∘ₗ sP) hρ p
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply,
    coe_ofProdLinearEquiv] at h
  rw [ofLoopExtension_ofProd, extendExtensionAction_ofProd, h, ← map_add, ← of_add,
    Prod.mk_add_mk, add_zero, zero_add]
  simp

/-- The extended action restricts to the given action along the embedding of the polynomial
residue central extension. -/
@[simp]
theorem extendExtensionAction_comp_ofLoopExtension (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) :
    extendExtensionAction ρ hρ ∘ₗ (ofLoopExtension Φ hΦ hΦs).toLinearMap = ρ :=
  LinearMap.ext fun x ↦ extendExtensionAction_ofLoopExtension ρ hρ x

/-- The polynomial embedding is compatible with the current sections. -/
private theorem ofLoopExtension_comp_section :
    (ofLoopExtension Φ hΦ hΦs).toLinearMap ∘ₗ sP = sC ∘ₗ (ofLoop R L).toLinearMap :=
  LinearMap.ext fun p ↦ by simp [coe_ofProdLinearEquiv]

/-- An action of the residue central extension of formal currents which is smooth on currents
restricts to an action of the polynomial residue central extension which is smooth on currents. -/
theorem IsSmooth.comp_ofLoopExtension {τ : ofTwoCocycle cC →ₗ[R] Module.End R M}
    (hτ : IsSmooth (τ ∘ₗ sC)) :
    IsLoopSmooth ((τ ∘ₗ (ofLoopExtension Φ hΦ hΦs).toLinearMap) ∘ₗ sP) := by
  rw [LinearMap.comp_assoc, ofLoopExtension_comp_section, ← LinearMap.comp_assoc]
  exact hτ.comp_ofLoop

/-- The extended action is smooth on currents. -/
theorem isSmooth_extendExtensionAction (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) : IsSmooth (extendExtensionAction ρ hρ ∘ₗ sC) := by
  rw [extendExtensionAction_comp_section]
  exact isSmooth_extendAction _ hρ

/-- An action of the residue central extension of formal currents which is smooth on currents is
the extended action exactly when it restricts to `ρ` along the polynomial embedding. -/
theorem eq_extendExtensionAction_iff (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) {τ : ofTwoCocycle cC →ₗ[R] Module.End R M}
    (hτ : IsSmooth (τ ∘ₗ sC)) :
    τ = extendExtensionAction ρ hρ ↔ τ ∘ₗ (ofLoopExtension Φ hΦ hΦs).toLinearMap = ρ := by
  refine ⟨fun h ↦ h ▸ extendExtensionAction_comp_ofLoopExtension ρ hρ, fun h ↦ ?_⟩
  -- On currents, both actions are smooth with the same restriction to polynomial currents.
  have hcur : τ ∘ₗ sC = extendAction (ρ ∘ₗ sP) hρ := by
    rw [eq_extendAction_iff _ hρ hτ, ← h]
    simp only [LinearMap.comp_assoc, ofLoopExtension_comp_section]
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd cC).surjective x
  -- Central elements lie in the image of the polynomial embedding.
  have hz : ofProd cC (0, z) = ofLoopExtension Φ hΦ hΦs (ofProd cP (0, zP z)) := by
    simp
  have hx : ofProd cC (u, z) = sC u + ofProd cC (0, z) := by
    simp [coe_ofProdLinearEquiv, ← of_add]
  have hu : τ (sC u) = extendExtensionAction ρ hρ (sC u) := by
    rw [← LinearMap.comp_apply τ, hcur, ← LinearMap.comp_apply (extendExtensionAction ρ hρ),
      extendExtensionAction_comp_section]
  rw [hx, map_add, map_add, hz, hu, extendExtensionAction_ofLoopExtension]
  simpa using congr($h (ofProd cP (0, zP z)))

/-- Central elements of the polynomial extension act by operators commuting with the extension of
the action on currents, when `ρ` takes brackets to commutators. -/
private theorem commute_extendAction (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP))
    (hρL : ∀ x y : ofTwoCocycle cP, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x) (z : ZP) (u : C) :
    ρ (ofProd cP (0, z)) * extendAction (ρ ∘ₗ sP) hρ u =
      extendAction (ρ ∘ₗ sP) hρ u * ρ (ofProd cP (0, z)) := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine (forall_comp_extendAction_eq_iff _ hρ hρ (ρ (ofProd cP (0, z)))).mpr
    (fun p ↦ ?_) u
  have hc := hρL (sP p) (ofProd cP (0, z))
  simp only [bracket_ofTwoCocycle, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply,
    coe_ofProdLinearEquiv, Equiv.symm_apply_apply, lie_zero, map_zero, trivial_lie_zero, add_zero,
    sub_zero, Prod.mk_zero_zero, of_zero] at hc ⊢
  exact (sub_eq_zero.mp hc.symm).symm

/-- The extended action takes brackets to commutators when `ρ` does. -/
theorem extendExtensionAction_lie (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP))
    (hρL : ∀ x y : ofTwoCocycle cP, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x)
    (x y : ofTwoCocycle cC) :
    extendExtensionAction ρ hρ ⁅x, y⁆ =
      extendExtensionAction ρ hρ x * extendExtensionAction ρ hρ y -
        extendExtensionAction ρ hρ y * extendExtensionAction ρ hρ x := by
  obtain ⟨⟨u, a⟩, rfl⟩ := (ofProd cC).surjective x
  obtain ⟨⟨v, b⟩, rfl⟩ := (ofProd cC).surjective y
  -- First compare the commutator of the current parts with the bracket of currents.
  have key : extendAction (ρ ∘ₗ sP) hρ ⁅u, v⁆ +
      ρ (ofProd cP (0, (TrivialLieModule.equiv R P R).symm (residuePairing R L Φ u v))) =
      extendAction (ρ ∘ₗ sP) hρ u * extendAction (ρ ∘ₗ sP) hρ v -
        extendAction (ρ ∘ₗ sP) hρ v * extendAction (ρ ∘ₗ sP) hρ u := by
    ext m
    obtain ⟨Mu, hu⟩ := exists_mem_orderSubmodule R L u
    obtain ⟨Mv, hv⟩ := exists_mem_orderSubmodule R L v
    obtain ⟨N, h₁, h₂, h₃, hNu, hNv⟩ := (eventually_apply_lie_trunc_eq _ hρ u v m |>.and <|
      eventually_apply_trunc_apply_trunc_eq _ hρ u v m |>.and <|
      eventually_apply_trunc_apply_trunc_eq _ hρ v u m |>.and <|
      eventually_ge_atTop (1 - Mu) |>.and <| eventually_ge_atTop (1 - Mv)).exists
    have h := congr($(hρL (sP (trunc R L N u)) (sP (trunc R L N v))) m)
    rw [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      ← h₁, ← h₂, ← h₃, ← residuePairing_ofLoop_trunc R L Φ hu hv (by omega : 0 < N + Mv)
        (by omega : 0 < Mu + N)]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, coe_ofProdLinearEquiv, LinearMap.coe_inl,
      Function.comp_apply, bracket_ofTwoCocycle, Equiv.symm_apply_apply,
      LoopAlgebra.twoCocycleOfBilinear_coe, twoCochain_val_apply,
      LoopAlgebra.twoCochainOfBilinear_apply_apply, trivial_lie_zero, add_zero, sub_zero,
      LinearMap.sub_apply, Module.End.mul_apply, residuePairing_ofLoop] at h ⊢
    rw [← h, ← LinearMap.add_apply, ← map_add, ← of_add, Prod.mk_add_mk, add_zero, zero_add]
  have hK (z : ZP) := commute_extendAction ρ hρ hρL z
  have hKK (z z' : ZP) : ρ (ofProd cP (0, z)) * ρ (ofProd cP (0, z')) =
      ρ (ofProd cP (0, z')) * ρ (ofProd cP (0, z)) := by
    have hc := hρL (ofProd cP (0, z)) (ofProd cP (0, z'))
    simp only [bracket_ofTwoCocycle, Equiv.symm_apply_apply, lie_zero, map_zero,
      trivial_lie_zero, add_zero, sub_zero, Prod.mk_zero_zero, of_zero] at hc
    exact sub_eq_zero.mp hc.symm
  simp only [bracket_ofTwoCocycle, Equiv.symm_apply_apply, twoCocycleOfBilinear_coe,
    twoCochain_val_apply, twoCochainOfBilinear_apply_apply, trivial_lie_zero, add_zero, sub_zero,
    extendExtensionAction_ofProd, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, key,
    add_mul, mul_add, hK]
  rw [hKK]
  abel

/-- A linear map intertwines two extended actions exactly when it intertwines the actions of the
polynomial residue central extension. -/
theorem forall_comp_extendExtensionAction_eq_iff (ρ : ofTwoCocycle cP →ₗ[R] Module.End R M)
    (hρ : IsLoopSmooth (ρ ∘ₗ sP)) {ρ' : ofTwoCocycle cP →ₗ[R] Module.End R M'}
    (hρ' : IsLoopSmooth (ρ' ∘ₗ sP)) (f : M →ₗ[R] M') :
    (∀ x, f ∘ₗ extendExtensionAction ρ hρ x = extendExtensionAction ρ' hρ' x ∘ₗ f) ↔
      ∀ x, f ∘ₗ ρ x = ρ' x ∘ₗ f := by
  refine ⟨fun h x ↦ by simpa using h (ofLoopExtension Φ hΦ hΦs x), fun h x ↦ ?_⟩
  obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd cC).surjective x
  have hu := (forall_comp_extendAction_eq_iff _ hρ hρ' f).mpr (fun p ↦ h _) u
  simp only [extendExtensionAction_ofProd, LinearMap.comp_add, LinearMap.add_comp, hu, h]

section LieHom

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation of the residue central extension of formal currents extending a
representation of the polynomial residue central extension which is smooth on currents. -/
def extendExtensionLieHom (ρ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M)
    (hρ : IsLoopSmooth (ρ.toLinearMap ∘ₗ sP)) : ofTwoCocycle cC →ₗ⁅R⁆ Module.End R M where
  __ := extendExtensionAction ρ.toLinearMap hρ
  map_lie' {x y} := (extendExtensionAction_lie ρ.toLinearMap hρ (fun x y ↦ by
    simp [LieRing.of_associative_ring_bracket]) x y).trans
      (LieRing.of_associative_ring_bracket _ _).symm

/-- The extended representation is the extended action. -/
@[simp]
theorem toLinearMap_extendExtensionLieHom (ρ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M)
    (hρ : IsLoopSmooth (ρ.toLinearMap ∘ₗ sP)) :
    (extendExtensionLieHom ρ hρ).toLinearMap = extendExtensionAction ρ.toLinearMap hρ :=
  (rfl)

/-- The extended representation restricts to the given representation along the embedding of the
polynomial residue central extension. -/
@[simp]
theorem extendExtensionLieHom_comp_ofLoopExtension (ρ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M)
    (hρ : IsLoopSmooth (ρ.toLinearMap ∘ₗ sP)) :
    (extendExtensionLieHom ρ hρ).comp (ofLoopExtension Φ hΦ hΦs) = ρ :=
  LieHom.ext fun x ↦ extendExtensionAction_ofLoopExtension ρ.toLinearMap hρ x

/-- Representations of the polynomial residue central extension which are smooth on currents
correspond to representations of the residue central extension of formal currents which are
smooth on currents, by extension and by restriction along `ofLoopExtension`. -/
def smoothExtensionLieHomEquiv :
    {ρ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M // IsLoopSmooth (ρ.toLinearMap ∘ₗ sP)} ≃
      {σ : ofTwoCocycle cC →ₗ⁅R⁆ Module.End R M // IsSmooth (σ.toLinearMap ∘ₗ sC)} where
  toFun ρ := ⟨extendExtensionLieHom ρ.1 ρ.2, isSmooth_extendExtensionAction _ ρ.2⟩
  invFun σ := ⟨σ.1.comp (ofLoopExtension Φ hΦ hΦs), σ.2.comp_ofLoopExtension⟩
  left_inv ρ := Subtype.ext (extendExtensionLieHom_comp_ofLoopExtension ρ.1 ρ.2)
  right_inv σ := Subtype.ext <| LieHom.ext fun x ↦ LinearMap.congr_fun
    ((eq_extendExtensionAction_iff _ _ σ.2).mpr rfl).symm x

/-- The correspondence sends a representation of the polynomial residue central extension to its
extension. -/
@[simp]
theorem coe_smoothExtensionLieHomEquiv_apply
    (ρ : {ρ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M // IsLoopSmooth (ρ.toLinearMap ∘ₗ sP)}) :
    (smoothExtensionLieHomEquiv ρ : ofTwoCocycle cC →ₗ⁅R⁆ Module.End R M) =
      extendExtensionLieHom ρ.1 ρ.2 :=
  (rfl)

/-- The inverse correspondence restricts along the embedding of the polynomial residue central
extension. -/
@[simp]
theorem coe_smoothExtensionLieHomEquiv_symm_apply
    (σ : {σ : ofTwoCocycle cC →ₗ⁅R⁆ Module.End R M // IsSmooth (σ.toLinearMap ∘ₗ sC)}) :
    (smoothExtensionLieHomEquiv.symm σ : ofTwoCocycle cP →ₗ⁅R⁆ Module.End R M) =
      σ.1.comp (ofLoopExtension Φ hΦ hΦs) :=
  (rfl)

end LieHom

end Extension

end TauCeti.CurrentAlgebra
