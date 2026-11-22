/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Prod

import Mathlib.Algebra.Lie.Derivation.Killing
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Reductive Cartan involutions

On a reductive Lie algebra `L = Z(L) ⊕ [L, L]`, the Killing form vanishes on the centre `Z(L)`, so
the Cartan-involution condition is imposed on the derived algebra `[L, L]`: a Lie algebra
automorphism `θ : L ≃ₗ⁅R⁆ L` is a **reductive Cartan involution**
(`LieEquiv.IsReductiveCartanInvolution`) when `θ` is involutive and its restriction
`θ.derivedSeriesCongr 1` to `[L, L]` is a Cartan involution.

Over any ordered field `K`, with no finite-dimensionality assumption on `L` itself, a
reductive Cartan involution forces `[L, L]` to be Killing, finite-dimensional, and semisimple,
forces `L` to be reductive (`HasCentralRadical K L`), and splits `L = Z(L) ⊕ [L, L]` (every
derivation of the finite-dimensional Killing algebra `[L, L]` is inner). Conversely, whenever
`L = Z(L) ⊕ [L, L]`, any involutive automorphism of `Z(L)` and any Cartan involution of `[L, L]`
extend uniquely via `LieEquiv.ofIsCompl` to a reductive Cartan involution of `L`, and both
eigenspaces `𝔨` and `𝔭` split across the centre and the derived ideal
(`LieEquiv.cartanPCenterDerivedEquiv`).

## Main definitions

* `LieEquiv.centerCongr` and `LieEquiv.derivedSeriesCongr`: the induced equivalences on the centre
  and the terms of the derived series.
* `LieEquiv.cartanPCenterDerivedEquiv`: linear splitting of `θ.cartanP` into its central and
  derived components when `L = Z(L) ⊕ [L, L]`.
* `LieEquiv.IsReductiveCartanInvolution`: predicate stating that `θ` is involutive and its
  restriction to `derivedSeries K L 1` is a Cartan involution.

## Main results

* `LieEquiv.isReductiveCartanInvolution_ofIsCompl_iff`: an automorphism built from `(θZ, θD)` on
  `Z(L) ⊕ [L, L]` is a reductive Cartan involution iff `θZ` is involutive and `θD` is a Cartan
  involution.
* `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical` and
  `LieEquiv.IsReductiveCartanInvolution.isCompl_center_derivedSeries`: a reductive Cartan
  involution over an ordered field forces `L` to be reductive and split as `Z(L) ⊕ [L, L]`.
* `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution` and
  `LieEquiv.IsReductiveCartanInvolution.isCartanInvolution_iff_center_eq_bot`: comparison with
  semisimple Cartan involutions.
* `LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top` and
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`: over `ℝ`, `ad x` is diagonalizable for
  every `x ∈ θ.cartanP`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2 and Chapter VII, §2.
-/

public section

open LieAlgebra

namespace LieEquiv

section Ring

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- A Lie equivalence preserves membership in the centre. -/
theorem apply_mem_center_iff (e : L ≃ₗ⁅R⁆ L') {x : L} :
    e x ∈ center R L' ↔ x ∈ center R L := by
  simp only [LieModule.mem_maxTrivSubmodule]
  constructor
  · intro hx y
    apply e.injective
    simp only [coe_toLieHom, e.map_lie, map_zero]
    exact hx (e y)
  · intro hx y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp only [coe_toLieHom]
    rw [← e.map_lie, hx z, map_zero]

/-- The Lie equivalence between centres induced by a Lie equivalence. -/
def centerCongr (e : L ≃ₗ⁅R⁆ L') : center R L ≃ₗ⁅R⁆ center R L' :=
  e.ofSubalgebras (center R L).toLieSubalgebra (center R L').toLieSubalgebra <| by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact e.apply_mem_center_iff.mpr hx
    · intro hy
      exact ⟨e.symm y, e.apply_mem_center_iff.mp (by simpa using hy), e.apply_symm_apply y⟩

/-- `centerCongr` agrees with `e` on underlying elements. -/
@[simp]
theorem coe_centerCongr (e : L ≃ₗ⁅R⁆ L') (x : center R L) :
    (e.centerCongr x : L') = e x := by
  rfl

/-- `centerCongr` commutes with `.symm`. -/
@[simp]
theorem centerCongr_symm (e : L ≃ₗ⁅R⁆ L') :
    e.centerCongr.symm = e.symm.centerCongr := by
  ext x
  rfl

/-- `centerCongr` preserves involutivity. -/
theorem involutive_centerCongr {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    Function.Involutive θ.centerCongr :=
  fun x ↦ Subtype.ext (hθ x)

/-- A Lie equivalence preserves membership in every term of the derived series. -/
@[simp]
theorem apply_mem_derivedSeries_iff (e : L ≃ₗ⁅R⁆ L') (k : ℕ) {x : L} :
    e x ∈ derivedSeries R L' k ↔ x ∈ derivedSeries R L k := by
  constructor
  · intro hx
    have h := LieIdeal.derivedSeries_map_le (f := e.symm.toLieHom) k (LieIdeal.mem_map hx)
    simpa using h
  · intro hx
    exact LieIdeal.derivedSeries_map_le (f := e.toLieHom) k (LieIdeal.mem_map hx)

/-- The Lie equivalence on the `k`-th term of the derived series induced by a Lie equivalence. -/
def derivedSeriesCongr (e : L ≃ₗ⁅R⁆ L') (k : ℕ) :
    derivedSeries R L k ≃ₗ⁅R⁆ derivedSeries R L' k :=
  e.ofSubalgebras (derivedSeries R L k).toLieSubalgebra (derivedSeries R L' k).toLieSubalgebra <| by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (e.apply_mem_derivedSeries_iff k).mpr hx
    · intro hy
      exact ⟨e.symm y, (e.apply_mem_derivedSeries_iff k).mp (by simpa using hy),
        e.apply_symm_apply y⟩

/-- `derivedSeriesCongr` agrees with `e` on underlying elements. -/
@[simp]
theorem coe_derivedSeriesCongr (e : L ≃ₗ⁅R⁆ L') (k : ℕ) (x : derivedSeries R L k) :
    (e.derivedSeriesCongr k x : L') = e x := by
  rfl

/-- `derivedSeriesCongr` commutes with `.symm`. -/
@[simp]
theorem derivedSeriesCongr_symm (e : L ≃ₗ⁅R⁆ L') (k : ℕ) :
    (e.derivedSeriesCongr k).symm = e.symm.derivedSeriesCongr k := by
  ext x
  rfl

/-- `derivedSeriesCongr` preserves involutivity. -/
theorem involutive_derivedSeriesCongr {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (k : ℕ) :
    Function.Involutive (θ.derivedSeriesCongr k) :=
  fun x ↦ Subtype.ext (hθ x)

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the centre recovers `θZ`. -/
@[simp]
theorem centerCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).centerCongr = θZ := by
  ext x
  exact ofIsCompl_apply_left h θZ θD x

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the derived ideal recovers `θD`. -/
@[simp]
theorem derivedSeriesCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).derivedSeriesCongr 1 = θD := by
  ext x
  exact ofIsCompl_apply_right h θZ θD x

/-- Any automorphism of `L = Z(L) ⊕ [L, L]` is determined by its restrictions to the centre and
the derived ideal. -/
theorem eq_ofIsCompl_centerCongr_derivedSeriesCongr (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    θ = ofIsCompl h θ.centerCongr (θ.derivedSeriesCongr 1) := by
  ext x
  obtain ⟨⟨z, d⟩, rfl⟩ :=
    (LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h).surjective x
  simp [map_add]

/-- When `L = Z(L) ⊕ [L, L]`, addition identifies the product of the `-1`-eigenspaces on `Z(L)` and
`[L, L]` with `θ.cartanP`. -/
noncomputable def cartanPCenterDerivedEquiv (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) ≃ₗ[R] θ.cartanP :=
  let f : (θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) →ₗ[R] θ.cartanP :=
    { toFun := fun p ↦ ⟨(p.1.val : L) + (p.2.val : L), by
        have h1 : θ p.1.val = -(p.1.val : L) := by
          simpa [coe_centerCongr] using congrArg Subtype.val (mem_cartanP.mp p.1.property)
        have h2 : θ p.2.val = -(p.2.val : L) := by
          simpa [coe_derivedSeriesCongr] using congrArg Subtype.val (mem_cartanP.mp p.2.property)
        rw [mem_cartanP, map_add, h1, h2, neg_add]⟩
      map_add' := fun p q ↦ by
        apply Subtype.ext
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, LieSubmodule.coe_add]
        abel
      map_smul' := fun c p ↦ by
        apply Subtype.ext
        simp [smul_add] }
  LinearEquiv.ofBijective f <| by
    let e := LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h
    constructor
    · intro p q hpq
      have heq : (p.1.val, p.2.val) = (q.1.val, q.2.val) := by
        apply e.injective
        simpa [e, f] using congrArg Subtype.val hpq
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))
    · intro x
      obtain ⟨⟨z, d⟩, hzd⟩ := e.surjective (x : L)
      have hsum : (z : L) + (d : L) = (x : L) := by simpa [e] using hzd
      have hx : θ (x : L) = -(x : L) := mem_cartanP.mp x.property
      have hneg : (θ.centerCongr z, θ.derivedSeriesCongr 1 d) = (-z, -d) := by
        apply e.injective
        simp only [coe_toLieHom, e, LieIdeal.prodEquivOfIsCompl_apply, coe_centerCongr,
          coe_derivedSeriesCongr, NegMemClass.coe_neg, ← map_add, hsum, hx]
        rw [← hsum, neg_add]
      have hz : z ∈ θ.centerCongr.cartanP :=
        mem_cartanP.mpr (congrArg Prod.fst hneg)
      have hd : d ∈ (θ.derivedSeriesCongr 1).cartanP :=
        mem_cartanP.mpr (congrArg Prod.snd hneg)
      exact ⟨(⟨z, hz⟩, ⟨d, hd⟩), Subtype.ext hsum⟩

/-- `cartanPCenterDerivedEquiv` acts by addition in `L`. -/
@[simp]
theorem coe_cartanPCenterDerivedEquiv_apply (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) :
    (θ.cartanPCenterDerivedEquiv h p : L) = (p.1.val : L) + (p.2.val : L) := by
  rfl

/-- When `L = Z(L) ⊕ [L, L]`, the fixed subalgebra splits as the supremum of its central and
derived parts. -/
theorem fixedSubalgebra_eq_sup_inf_center_inf_derivedSeries (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    θ.toLieHom.fixedSubalgebra =
      (θ.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ⊔
        (θ.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  let e := LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h
  obtain ⟨⟨z, d⟩, hzd⟩ := e.surjective x
  have hsum : (z : L) + (d : L) = x := by simpa [e] using hzd
  have hfix : (θ.centerCongr z, θ.derivedSeriesCongr 1 d) = (z, d) := by
    apply e.injective
    simp only [coe_toLieHom, e, LieIdeal.prodEquivOfIsCompl_apply, coe_centerCongr,
      coe_derivedSeriesCongr, ← map_add, hsum]
    exact LieHom.mem_fixedSubalgebra.mp hx
  have hz : (z : L) ∈ θ.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra :=
    ⟨LieHom.mem_fixedSubalgebra.mpr (congrArg (fun p ↦ (p.1 : L)) hfix), z.property⟩
  have hd : (d : L) ∈ θ.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra :=
    ⟨LieHom.mem_fixedSubalgebra.mpr (congrArg (fun p ↦ (p.2 : L)) hfix), d.property⟩
  have hz' : (z : L) ∈ (θ.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ⊔
      (θ.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra) :=
    le_sup_left (a := θ.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) hz
  have hd' : (d : L) ∈ (θ.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ⊔
      (θ.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra) :=
    le_sup_right (b := θ.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra) hd
  rw [← hsum]
  exact LieSubalgebra.add_mem _ hz' hd'

end Ring

section Field

variable {K L L' : Type*} [Field K] [LinearOrder K]
  [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']

/-- A **reductive Cartan involution** of a Lie algebra `L`: an involutive Lie algebra automorphism
whose restriction to the derived ideal `[L, L]` is a Cartan involution. -/
def IsReductiveCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop :=
  Function.Involutive θ ∧ (θ.derivedSeriesCongr 1).IsCartanInvolution

/-- Unfolded characterization of a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_iff (θ : L ≃ₗ⁅K⁆ L) :
    θ.IsReductiveCartanInvolution ↔
      Function.Involutive θ ∧ (θ.derivedSeriesCongr 1).IsCartanInvolution :=
  Iff.rfl

/-- Transport of `IsReductiveCartanInvolution` along an intertwining Lie equivalence. -/
theorem isReductiveCartanInvolution_iff_of_intertwine (e : L ≃ₗ⁅K⁆ L')
    {θ : L ≃ₗ⁅K⁆ L} {θ' : L' ≃ₗ⁅K⁆ L'} (h : ∀ x, θ' (e x) = e (θ x)) :
    θ'.IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution := by
  have hint : ∀ x : derivedSeries K L 1,
      θ'.derivedSeriesCongr 1 (e.derivedSeriesCongr 1 x) =
        e.derivedSeriesCongr 1 (θ.derivedSeriesCongr 1 x) :=
    fun x ↦ Subtype.ext (h x)
  have hinv : Function.Involutive θ' ↔ Function.Involutive θ := by
    constructor
    · intro h' x
      apply e.injective
      simp only [coe_toLieHom]
      rw [← h, ← h, h' (e x)]
    · intro h' y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [coe_toLieHom]
      rw [h, h, h' x]
  exact and_congr hinv (isCartanInvolution_iff_of_intertwine (e.derivedSeriesCongr 1) hint)

/-- Conjugating a Lie automorphism preserves the reductive Cartan-involution property. -/
theorem isReductiveCartanInvolution_conj (e : L ≃ₗ⁅K⁆ L') (θ : L ≃ₗ⁅K⁆ L) :
    ((e.symm.trans θ).trans e).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution :=
  isReductiveCartanInvolution_iff_of_intertwine e fun x ↦ by simp

/-- On `L = Z(L) ⊕ [L, L]`, an automorphism built from `(θZ, θD)` is a reductive Cartan involution
if and only if `θZ` is involutive and `θD` is a Cartan involution. -/
theorem isReductiveCartanInvolution_ofIsCompl_iff (h : IsCompl (center K L) (derivedSeries K L 1))
    (θZ : center K L ≃ₗ⁅K⁆ center K L) (θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1) :
    (ofIsCompl h θZ θD).IsReductiveCartanInvolution ↔
      Function.Involutive θZ ∧ θD.IsCartanInvolution := by
  rw [IsReductiveCartanInvolution, involutive_ofIsCompl_iff, derivedSeriesCongr_ofIsCompl]
  exact ⟨fun ⟨⟨hZ, _⟩, hD⟩ ↦ ⟨hZ, hD⟩, fun ⟨hZ, hD⟩ ↦ ⟨⟨hZ, hD.involutive⟩, hD⟩⟩

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- A reductive Cartan involution is involutive. -/
theorem involutive (hθ : θ.IsReductiveCartanInvolution) : Function.Involutive θ :=
  hθ.1

/-- The restriction of a reductive Cartan involution to `[L, L]` is a Cartan involution. -/
theorem isCartanInvolution_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    (θ.derivedSeriesCongr 1).IsCartanInvolution :=
  hθ.2

/-- The restriction of a reductive Cartan involution to the centre is involutive. -/
theorem involutive_centerCongr (hθ : θ.IsReductiveCartanInvolution) :
    Function.Involutive θ.centerCongr :=
  LieEquiv.involutive_centerCongr hθ.1

variable [IsStrictOrderedRing K]

/-- The derived algebra `[L, L]` has nondegenerate Killing form. -/
theorem isKilling_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsKilling K (derivedSeries K L 1) :=
  hθ.2.isKilling

/-- The derived algebra `[L, L]` is finite-dimensional over `K`. -/
theorem finite_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    Module.Finite K (derivedSeries K L 1) :=
  hθ.2.finiteDimensional

/-- The derived algebra `[L, L]` of a Lie algebra with a reductive Cartan involution is
semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsSemisimple K (derivedSeries K L 1) :=
  hθ.2.isSemisimple

/-- **Reductivity from a reductive Cartan involution.** A Lie algebra over an ordered field
admitting a reductive Cartan involution has central radical, with no finite-dimensionality
assumption on `L`. -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.HasCentralRadical K L := by
  have : LieAlgebra.IsSemisimple K (derivedSeries K L 1) := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

/-- **Centre/derived splitting from a reductive Cartan involution.** A Lie algebra over an ordered
field admitting a reductive Cartan involution splits as `L = Z(L) ⊕ [L, L]`.

No finite-dimensionality assumption on `L` is needed: `[L, L]` is automatically finite-dimensional
and Killing, so every derivation of `[L, L]` is inner (`LieDerivation.IsKilling.exists_eq_ad`). -/
theorem isCompl_center_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsCompl (center K L) (derivedSeries K L 1) := by
  have : LieAlgebra.IsKilling K (derivedSeries K L 1) := hθ.isKilling_derivedSeries
  have : Module.Finite K (derivedSeries K L 1) := hθ.finite_derivedSeries
  have hcenterD : center K (derivedSeries K L 1) = ⊥ := LieAlgebra.center_eq_bot K _
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro x ⟨hxZ, hxD⟩
    have hmem : (⟨x, hxD⟩ : derivedSeries K L 1) ∈ center K (derivedSeries K L 1) := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro y
      exact Subtype.ext ((LieModule.mem_maxTrivSubmodule K L L x).mp hxZ y)
    rw [hcenterD] at hmem
    exact congrArg Subtype.val hmem
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    -- The adjoint action of `x` on `[L, L]` is a derivation of a finite-dimensional Killing
    -- algebra, hence equals `ad d` for some `d ∈ [L, L]`.
    let δ : LieDerivation K (derivedSeries K L 1) (derivedSeries K L 1) :=
      { toFun := fun u ↦ ⟨⁅x, (u : L)⁆, LieAlgebra.lie_mem_derivedSeries_one x u⟩
        map_add' := fun u v ↦ Subtype.ext (by simp [lie_add])
        map_smul' := fun c u ↦ Subtype.ext (by simp [lie_smul])
        leibniz' := fun u v ↦ Subtype.ext <| by
          -- Coerce the ideal brackets to `L` to apply the Jacobi identity.
          change ⁅x, ⁅(u : L), (v : L)⁆⁆ = ⁅(u : L), ⁅x, (v : L)⁆⁆ - ⁅(v : L), ⁅x, (u : L)⁆⁆
          rw [leibniz_lie, ← lie_skew (v : L) ⁅x, (u : L)⁆, sub_neg_eq_add, add_comm] }
    obtain ⟨d, hd⟩ := LieDerivation.IsKilling.exists_eq_ad δ
    have hcomm (u : derivedSeries K L 1) : ⁅x - (d : L), (u : L)⁆ = 0 := by
      have hu : ⁅(d : L), (u : L)⁆ = ⁅x, (u : L)⁆ := by
        simpa [δ] using congrArg (fun f ↦ (f u : L)) hd
      rw [sub_lie, hu, sub_self]
    have hxdZ : x - (d : L) ∈ center K L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro y
      have hmem : (⟨⁅x - (d : L), y⁆, LieAlgebra.lie_mem_derivedSeries_one _ y⟩ :
          derivedSeries K L 1) ∈ center K (derivedSeries K L 1) := by
        rw [LieModule.mem_maxTrivSubmodule]
        intro u
        apply Subtype.ext
        have h1 : ⁅(u : L), x - (d : L)⁆ = 0 := by
          rw [← lie_skew, hcomm u, neg_zero]
        have h2 : ⁅x - (d : L), ⁅(u : L), y⁆⁆ = 0 :=
          hcomm ⟨⁅(u : L), y⁆, LieAlgebra.lie_mem_derivedSeries_one (u : L) y⟩
        -- Unfold the subtype bracket on `derivedSeries K L 1` to apply the Jacobi identity in `L`.
        change ⁅(u : L), ⁅x - (d : L), y⁆⁆ = 0
        rw [leibniz_lie, h1, zero_lie, zero_add, h2]
      rw [hcenterD] at hmem
      have hzero : ⁅x - (d : L), y⁆ = 0 := congrArg Subtype.val hmem
      rw [← lie_skew, hzero, neg_zero]
    have hx_eq : x = (x - (d : L)) + (d : L) := (sub_add_cancel x (d : L)).symm
    rw [hx_eq]
    have hleft : x - (d : L) ∈ center K L ⊔ derivedSeries K L 1 :=
      le_sup_left (a := center K L) hxdZ
    have hright : (d : L) ∈ center K L ⊔ derivedSeries K L 1 :=
      le_sup_right (b := derivedSeries K L 1) d.property
    exact (center K L ⊔ derivedSeries K L 1).add_mem hleft hright

/-- A reductive Cartan involution equals the automorphism reconstructed from its restrictions to
the centre and the derived ideal. -/
theorem eq_ofIsCompl (hθ : θ.IsReductiveCartanInvolution) :
    θ = ofIsCompl hθ.isCompl_center_derivedSeries θ.centerCongr (θ.derivedSeriesCongr 1) :=
  θ.eq_ofIsCompl_centerCongr_derivedSeriesCongr hθ.isCompl_center_derivedSeries

end IsReductiveCartanInvolution

variable [IsStrictOrderedRing K]

/-- Every semisimple Cartan involution is in particular a reductive Cartan involution, since a
Killing Lie algebra over a field is perfect. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) : θ.IsReductiveCartanInvolution := by
  have : LieAlgebra.IsKilling K L := hθ.isKilling
  have htop : derivedSeries K L 1 = ⊤ := TauCeti.derivedSeries_one_eq_top_of_isKilling K L
  let e : derivedSeries K L 1 ≃ₗ⁅K⁆ L :=
    LieEquiv.ofBijective (derivedSeries K L 1).incl
      ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, htop ▸ LieSubmodule.mem_top x⟩, rfl⟩⟩
  refine ⟨hθ.involutive, ?_⟩
  exact (isCartanInvolution_iff_of_intertwine e (fun _ ↦ rfl)).mp hθ

/-- A reductive Cartan involution is a (semisimple) Cartan involution if and only if the centre
vanishes. -/
theorem IsReductiveCartanInvolution.isCartanInvolution_iff_center_eq_bot {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) :
    θ.IsCartanInvolution ↔ center K L = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    have had : ad K L x = 0 := by
      ext z
      rw [ad_apply, LinearMap.zero_apply, ← lie_skew,
        (LieModule.mem_maxTrivSubmodule K L L x).mp hx z, neg_zero]
    exact h.isKilling.killingForm_nondegenerate.1 x fun y ↦ by
      rw [killingForm_apply_apply, had]
      simp
  · intro hZ
    have htop : derivedSeries K L 1 = ⊤ := by
      have hc := hθ.isCompl_center_derivedSeries
      rw [hZ] at hc
      rw [← hc.sup_eq_top, bot_sup_eq]
    let e : derivedSeries K L 1 ≃ₗ⁅K⁆ L :=
      LieEquiv.ofBijective (derivedSeries K L 1).incl
        ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, htop ▸ LieSubmodule.mem_top x⟩, rfl⟩⟩
    exact (isCartanInvolution_iff_of_intertwine e (fun _ ↦ rfl)).mpr hθ.2

end Field

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsReductiveCartanInvolution

/-- **Diagonalizability of `ad x` on `𝔭` for a reductive Cartan involution.** Over `ℝ`, for every
`x ∈ θ.cartanP`, the eigenspaces of `ad x` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have hc := hθ.isCompl_center_derivedSeries
  obtain ⟨⟨z, d⟩, hzd⟩ := (θ.cartanPCenterDerivedEquiv hc).surjective ⟨x, hx⟩
  have hx_eq : x = (z.val : L) + (d.val : L) := (congrArg Subtype.val hzd).symm
  have had_eq (y : L) : ad ℝ L x y = ⁅(d.val : L), y⁆ := by
    have hz : ⁅(z.val : L), y⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule ℝ L L z.val).mp z.val.property y, neg_zero]
    rw [ad_apply, hx_eq, add_lie, hz, zero_add]
  rw [eq_top_iff]
  have hZ : (center ℝ L).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    refine le_trans ?_ (le_iSup (fun μ ↦ Module.End.eigenspace (ad ℝ L x) μ) 0)
    intro w hw
    rw [Module.End.mem_eigenspace_iff, zero_smul, ad_apply,
      (LieModule.mem_maxTrivSubmodule ℝ L L w).mp hw x]
  have hD : (derivedSeries ℝ L 1).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    have hspan := hθ.2.iSup_eigenspace_ad_eq_top d.property
    intro w hw
    have hw' : (⟨w, hw⟩ : derivedSeries ℝ L 1) ∈
        ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ (derivedSeries ℝ L 1) d.val) μ := by
      rw [hspan]
      exact Submodule.mem_top
    have hmap : Submodule.map (derivedSeries ℝ L 1).incl.toLinearMap
        (⨆ μ : ℝ, Module.End.eigenspace (ad ℝ (derivedSeries ℝ L 1) d.val) μ) ≤
        ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun μ ↦ ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hu
      rw [Module.End.mem_eigenspace_iff, had_eq]
      exact congrArg Subtype.val hu
    exact hmap ⟨⟨w, hw⟩, hw', rfl⟩
  have hsup : (center ℝ L).toSubmodule ⊔ (derivedSeries ℝ L 1).toSubmodule = ⊤ :=
    (LieSubmodule.isCompl_toSubmodule.mpr hc).sup_eq_top
  rw [← hsup]
  exact sup_le hZ hD

/-- For a reductive Cartan involution of a real Lie algebra and every `x ∈ θ.cartanP`, the adjoint
operator `ad x` is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsReductiveCartanInvolution

end Real

end LieEquiv
