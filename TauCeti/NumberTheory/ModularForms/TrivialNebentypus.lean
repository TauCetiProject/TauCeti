/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# The two spellings of `M_k(Γ₀(N))`

There are two ways to say "modular form of level `N` with trivial nebentypus": as a modular
form for the bare congruence subgroup `Γ₀(N)`, and as an element of the character space
`M_k(Γ₁(N), χ)` of `TauCeti.NumberTheory.ModularForms.DiamondOperators` for the trivial
character `χ = 1`. The ModularForms roadmap flags the clash and pins its resolution: prove the
two isomorphic, then use `M_k(Γ₀(N))` as the default spelling and convert to it. This file is
that milestone, for modular forms (`TauCeti.modFormCharSpaceOneEquiv`) and for cusp forms
(`TauCeti.cuspFormCharSpaceOneEquiv`), both stated for `N ≠ 0`.

Both directions are instances of the generic subgroup-change API of
`TauCeti.NumberTheory.ModularForms.Basic`. Restricting a `Γ₀(N)`-form to `Γ₁(N)`
(`ModularForm.ofLe`) is unconditional, and the resulting form has trivial nebentypus because
the diamond operators are slashes by elements of `Γ₀(N)`. Conversely, a `Γ₁(N)`-form with
trivial nebentypus is `Γ₀(N)`-slash invariant by the nebentypus criterion
`mem_modFormCharSpace_iff_nebentypus`, and it is bounded (resp. zero) at every cusp of `Γ₀(N)`
because for `N ≠ 0` the groups `Γ₀(N)` and `Γ₁(N)` are arithmetic, hence share the cusps of
`SL(2, ℤ)` (`Subgroup.IsArithmetic.isCusp_of_isCusp`); this is `ModularForm.ofSlashInvariant`.
Both constructions preserve the underlying function `ℍ → ℂ`, so the resulting bijections are
`ℂ`-linear and conversion in either direction costs nothing: see the `coe_…_apply` lemmas
below.

The hypothesis `N ≠ 0` is therefore needed only for that converse direction: the
characterisations of trivial nebentypus and the results about restricting a `Γ₀(N)`-form hold
at every level, while the range equalities and the two equivalences assume `[NeZero N]`.

Note what the isomorphism is *not*: `M_k(Γ₁(N), 1)` is a `Submodule` of `M_k(Γ₁(N))`, so the
statement is that a submodule of the level-`Γ₁(N)` space is linearly equivalent to another
space of forms, not an equality of types.

## Main definitions

* `TauCeti.modFormCharSpaceOneEquiv`, `TauCeti.cuspFormCharSpaceOneEquiv`: for `N ≠ 0`, the
  `ℂ`-linear equivalences `M_k(Γ₁(N), 1) ≃ₗ M_k(Γ₀(N))` and `S_k(Γ₁(N), 1) ≃ₗ S_k(Γ₀(N))`.
* `TauCeti.cuspFormTraceGamma0`: for `N ≠ 0`, Mathlib's trace `CuspForm.trace` from `Γ₁(N)` to
  `Γ₀(N)`, as a `ℂ`-linear map `S_k(Γ₁(N)) →ₗ S_k(Γ₀(N))`.

## Main results

* `TauCeti.mem_modFormCharSpace_one_iff`, `TauCeti.mem_cuspFormCharSpace_one_iff`: trivial
  nebentypus means `Γ₀(N)`-slash invariance.
* `TauCeti.mem_modFormCharSpace_one_iff_diamondOp`,
  `TauCeti.mem_cuspFormCharSpace_one_iff_diamondOpCusp`: equivalently, being fixed by every
  diamond operator.
* `TauCeti.modFormCharSpace_one_eq_range`, `TauCeti.cuspFormCharSpace_one_eq_range`: for
  `N ≠ 0`, the trivial-nebentypus space is the image of the restriction map from level
  `Γ₀(N)`.
* `TauCeti.coe_trace_eq_sum_diamondOpCusp`: the trace from `Γ₁(N)` to `Γ₀(N)` is the sum of
  the diamond operators `∑ᵤ ⟨u⟩`.
* `TauCeti.sum_diamondOpCusp_mem_cuspFormCharSpace_one`: a diamond sum along a surjection has
  trivial nebentypus.
* `TauCeti.cuspFormTraceGamma0_ofLe`: tracing a restricted `Γ₀(N)` form multiplies it by
  `#(ZMod N)ˣ`.
* `TauCeti.cuspFormTraceGamma0_levelRaise`: trace commutes with level raising when the lower-level
  diamond sum comes from a `Γ₀` cusp form.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.1
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ}

/-! ### Trivial nebentypus is `Γ₀(N)`-invariance -/

/-- A modular form for `Γ₁(N)` has trivial nebentypus exactly when it is `Γ₀(N)`-slash
invariant. -/
theorem mem_modFormCharSpace_one_iff (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  refine ⟨?_, fun h g ↦ ?_⟩
  · rintro h - ⟨g, hg, rfl⟩
    simpa using h ⟨g, hg⟩
  · simpa using h _ (Subgroup.mem_map_of_mem _ g.2)

/-- A cusp form for `Γ₁(N)` has trivial nebentypus exactly when it is `Γ₀(N)`-slash
invariant. -/
theorem mem_cuspFormCharSpace_one_iff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f := by
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  refine ⟨?_, fun h g ↦ ?_⟩
  · rintro h - ⟨g, hg, rfl⟩
    simpa using h ⟨g, hg⟩
  · simpa using h _ (Subgroup.mem_map_of_mem _ g.2)

/-- Trivial nebentypus means being fixed by every diamond operator. -/
theorem mem_modFormCharSpace_one_iff_diamondOp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔ ∀ d : (ZMod N)ˣ, diamondOp k d f = f := by
  simp

/-- Trivial nebentypus means being fixed by every diamond operator. -/
theorem mem_cuspFormCharSpace_one_iff_diamondOpCusp (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ d : (ZMod N)ˣ, diamondOpCusp k d f = f := by
  simp

/-- Summing the diamond operators of level `M` along a surjection `(ZMod N)ˣ → (ZMod M)ˣ`
gives a form of trivial nebentypus. -/
theorem sum_diamondOpCusp_mem_cuspFormCharSpace_one {M : ℕ} [NeZero N]
    {φ : (ZMod N)ˣ →* (ZMod M)ˣ} (hφ : Function.Surjective φ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∑ u, diamondOpCusp k (φ u) g ∈ cuspFormCharSpace k (1 : (ZMod M)ˣ →* ℂˣ) := by
  rw [mem_cuspFormCharSpace_one_iff_diamondOpCusp]
  intro v
  obtain ⟨w, rfl⟩ := hφ v
  rw [map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ fun u ↦ by
    rw [Equiv.coe_mulLeft, map_mul, diamondOpCusp_mul, LinearMap.comp_apply]

/-! ### Restricting a `Γ₀(N)`-form to `Γ₁(N)` -/

/-- Restricted to `Γ₁(N)`, a modular form for `Γ₀(N)` has trivial nebentypus. -/
theorem ofLe_mem_modFormCharSpace_one (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f ∈
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) :=
  (mem_modFormCharSpace_one_iff _).mpr fun γ hγ ↦ by
    simpa using f.slash_action_eq' γ hγ

/-- Restricted to `Γ₁(N)`, a cusp form for `Γ₀(N)` has trivial nebentypus. -/
theorem ofLe_mem_cuspFormCharSpace_one (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) :=
  (mem_cuspFormCharSpace_one_iff _).mpr fun γ hγ ↦ by
    simpa using f.slash_action_eq' γ hγ

/-- The diamond operators fix the restriction of a `Γ₀(N)`-form: they are slashes by elements
of `Γ₀(N)`, under which such a form is already invariant. -/
theorem diamondOp_ofLe (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ) :
    diamondOp k d (ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f) =
      ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (mem_modFormCharSpace_one_iff_diamondOp _).mp (ofLe_mem_modFormCharSpace_one f) d

/-- The diamond operators fix the restriction of a `Γ₀(N)`-cusp form. -/
theorem diamondOpCusp_ofLe (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ) :
    diamondOpCusp k d (CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f) =
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (mem_cuspFormCharSpace_one_iff_diamondOpCusp _).mp (ofLe_mem_cuspFormCharSpace_one f) d

/-- The trivial-nebentypus space is exactly the image of `M_k(Γ₀(N))` under restriction. -/
theorem modFormCharSpace_one_eq_range [NeZero N] :
    modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) =
      LinearMap.range (ModularForm.ofLeₗ (k := k) (Gamma1_map_le_Gamma0_map N)) :=
  Submodule.ext fun f ↦
    (mem_modFormCharSpace_one_iff f).trans
      (ModularForm.mem_range_ofLeₗ_iff _ Subgroup.IsArithmetic.isCusp_of_isCusp f).symm

/-- The trivial-nebentypus space is exactly the image of `S_k(Γ₀(N))` under restriction. -/
theorem cuspFormCharSpace_one_eq_range [NeZero N] :
    cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) =
      LinearMap.range (CuspForm.ofLeₗ (k := k) (Gamma1_map_le_Gamma0_map N)) :=
  Submodule.ext fun f ↦
    (mem_cuspFormCharSpace_one_iff f).trans
      (CuspForm.mem_range_ofLeₗ_iff _ Subgroup.IsArithmetic.isCusp_of_isCusp f).symm

/-! ### The isomorphisms

The two equivalences are deliberately not `@[expose]`, so the `coe_…` lemmas recording that
they preserve the underlying function are written `(rfl)` rather than `rfl`: the parentheses opt
out of exporting the definitional equality, which those lemmas themselves replace downstream.
-/

/-- **The two spellings of `M_k(Γ₀(N))` agree**: the trivial-nebentypus character space
`M_k(Γ₁(N), 1)` is `ℂ`-linearly isomorphic to the space `M_k(Γ₀(N))` of modular forms for the
bare congruence subgroup `Γ₀(N)`, by an isomorphism preserving the underlying function on `ℍ`
(`coe_modFormCharSpaceOneEquiv_apply`). -/
noncomputable def modFormCharSpaceOneEquiv (N : ℕ) [NeZero N] (k : ℤ) :
    modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ((mem_modFormCharSpace_one_iff _).mp f.2)
  map_add' _ _ := ModularForm.ext fun _ ↦ by simp
  map_smul' _ _ := ModularForm.ext fun _ ↦ by simp
  invFun f := ⟨ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f,
    ofLe_mem_modFormCharSpace_one f⟩
  left_inv _ := Subtype.ext (ModularForm.ext fun _ ↦ by simp)
  right_inv _ := ModularForm.ext fun _ ↦ by simp

/-- `modFormCharSpaceOneEquiv` does not change the underlying function on `ℍ`: a
trivial-nebentypus form is converted to a `Γ₀(N)`-form by re-reading it, not by transporting
it. -/
@[simp]
theorem coe_modFormCharSpaceOneEquiv_apply [NeZero N]
    (f : modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ⇑(modFormCharSpaceOneEquiv N k f) = ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ModularForm.coe_ofSlashInvariant _ _ _

/-- The inverse of `modFormCharSpaceOneEquiv` is the restriction `ModularForm.ofLe` of a
`Γ₀(N)`-form to `Γ₁(N)`; in particular it too preserves the underlying function on `ℍ`. -/
@[simp]
theorem coe_modFormCharSpaceOneEquiv_symm_apply [NeZero N]
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (((modFormCharSpaceOneEquiv N k).symm f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (rfl)

/-- **The two spellings of `S_k(Γ₀(N))` agree**: the cusp-form analogue of
`modFormCharSpaceOneEquiv`. -/
noncomputable def cuspFormCharSpaceOneEquiv (N : ℕ) [NeZero N] (k : ℤ) :
    cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := CuspForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ((mem_cuspFormCharSpace_one_iff _).mp f.2)
  map_add' _ _ := CuspForm.ext fun _ ↦ by simp
  map_smul' _ _ := CuspForm.ext fun _ ↦ by simp
  invFun f := ⟨CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f, ofLe_mem_cuspFormCharSpace_one f⟩
  left_inv _ := Subtype.ext (CuspForm.ext fun _ ↦ by simp)
  right_inv _ := CuspForm.ext fun _ ↦ by simp

/-- `cuspFormCharSpaceOneEquiv` does not change the underlying function on `ℍ`: a
trivial-nebentypus cusp form is converted to a `Γ₀(N)`-cusp form by re-reading it, not by
transporting it. -/
@[simp]
theorem coe_cuspFormCharSpaceOneEquiv_apply [NeZero N]
    (f : cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ⇑(cuspFormCharSpaceOneEquiv N k f) = ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  CuspForm.coe_ofSlashInvariant _ _ _

/-- The inverse of `cuspFormCharSpaceOneEquiv` is the restriction `CuspForm.ofLe` of a
`Γ₀(N)`-cusp form to `Γ₁(N)`; in particular it too preserves the underlying function on `ℍ`. -/
@[simp]
theorem coe_cuspFormCharSpaceOneEquiv_symm_apply [NeZero N]
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (((cuspFormCharSpaceOneEquiv N k).symm f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (rfl)

/-! ### The trace from `Γ₁(N)` to `Γ₀(N)` is the diamond sum -/

section Trace

/-- For `N ≠ 0`, `Γ₁(N)` has finite index in `Γ₀(N)`, so the trace from `Γ₁(N)` to `Γ₀(N)` is
defined. -/
instance instIsFiniteRelIndexGamma1MapGamma0Map (N : ℕ) [NeZero N] :
    ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma0 N).map (mapGL ℝ)) :=
  Subgroup.IsFiniteRelIndex.map (mapGL ℝ)
    (Subgroup.isFiniteRelIndex_of_finiteIndex (H := Gamma1 N) (K := Gamma0 N))

/-- A representative in `(Gamma0 N).map (mapGL ℝ)`, pulled back to `Γ₀(N)` and mapped forward
again, is itself. -/
private lemma mapGL_equivMapOfInjective_symm (y : (Gamma0 N).map (mapGL ℝ)) :
    mapGL ℝ (((Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ) mapGL_injective).symm y :
      Gamma0 N) : SL(2, ℤ)) = y := by
  rw [← Subgroup.coe_equivMapOfInjective_apply (Gamma0 N) (mapGL ℝ) mapGL_injective,
    MulEquiv.apply_symm_apply]

/-- The cosets of `Γ₁(N)` in `Γ₀(N)` are indexed by `Gamma0Map` and hence by the diamond
operators. -/
private noncomputable def cosetDiamondEquiv (N : ℕ) :
    (Gamma0 N).map (mapGL ℝ) ⧸
      ((Gamma1 N).map (mapGL ℝ)).subgroupOf ((Gamma0 N).map (mapGL ℝ)) ≃ (ZMod N)ˣ := by
  let e := Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ) mapGL_injective
  let G := (Gamma1 N).map (mapGL ℝ)
  let H := (Gamma0 N).map (mapGL ℝ)
  have key (y : H) : (y : GL (Fin 2) ℝ) ∈ G ↔
      (e.symm y) ∈ (Gamma0Map N).toHomUnits.ker := by
    rw [← mapGL_equivMapOfInjective_symm y, Subgroup.mem_map_iff_mem mapGL_injective,
      MonoidHom.mem_ker, mem_Gamma1_iff]
    simp [Gamma0Map_apply, MonoidHom.coe_toHomUnits, Units.ext_iff, e]
  let E : H ⧸ G.subgroupOf H ≃ (Gamma0 N) ⧸ (Gamma0Map N).toHomUnits.ker :=
    Quotient.congr e.symm.toEquiv (by
      intro x y
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
        Subgroup.mem_subgroupOf, key]
      simp)
  exact E.trans (QuotientGroup.quotientKerEquivOfSurjective
    (Gamma0Map N).toHomUnits Gamma0Map_toHomUnits_surjective).toEquiv

private lemma cosetDiamondEquiv_mk (N : ℕ) (g : Gamma0 N) :
    cosetDiamondEquiv N
      (QuotientGroup.mk (Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ)
        mapGL_injective g)) = (Gamma0Map N).toHomUnits g := by
  unfold cosetDiamondEquiv
  dsimp only [Equiv.trans_apply]
  rw [Quotient.congr_mk]
  simp [QuotientGroup.quotientKerEquivOfSurjective]

/-- `cosetDiamondEquiv` sends a coset to the diamond index of its chosen representative. -/
private lemma cosetDiamondEquiv_apply (N : ℕ)
    (q : (Gamma0 N).map (mapGL ℝ) ⧸
      ((Gamma1 N).map (mapGL ℝ)).subgroupOf ((Gamma0 N).map (mapGL ℝ))) :
    cosetDiamondEquiv N q = (Gamma0Map N).toHomUnits
      ((Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ) mapGL_injective).symm q.out) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q,
    ← (Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ) mapGL_injective).apply_symm_apply q.out]
  exact cosetDiamondEquiv_mk N _

/-- **Mathlib's cusp-form trace from `Γ₁(N)` to `Γ₀(N)` is the diamond sum** `∑ᵤ ⟨u⟩ F`. -/
theorem coe_trace_eq_sum_diamondOpCusp [NeZero N] (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.trace ((Gamma0 N).map (mapGL ℝ)) F) =
      ⇑(∑ u : (ZMod N)ˣ, diamondOpCusp k u F) := by
  let qFintype : Fintype (((Gamma0 N).map (mapGL ℝ)) ⧸
      ((Gamma1 N).map (mapGL ℝ)).subgroupOf ((Gamma0 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  -- the trace slashes by the inverse of each representative, hence the `Equiv.inv`
  let E := (cosetDiamondEquiv N).trans (Equiv.inv (ZMod N)ˣ)
  funext τ
  rw [CuspForm.coe_trace]
  simp only [Finset.sum_apply]
  have hsum : (∑ u : (ZMod N)ˣ, diamondOpCusp k u F) τ =
      ∑ u : (ZMod N)ˣ, (diamondOpCusp k u F) τ := by simp
  rw [hsum]
  apply @Fintype.sum_equiv _ _ _ qFintype inferInstance _ E
  intro q
  let g : Gamma0 N := (Subgroup.equivMapOfInjective (Gamma0 N) (mapGL ℝ) mapGL_injective).symm q.out
  have hg : (Gamma0Map N).toHomUnits g⁻¹ = E q := by
    rw [Equiv.trans_apply, Equiv.inv_apply, cosetDiamondEquiv_apply, map_inv]
  conv_lhs => rw [← Quotient.out_eq q]
  rw [SlashInvariantForm.quotientFunc_mk, coe_diamondOpCusp k (E q) g⁻¹ hg F]
  simpa only [Subgroup.coe_inv, map_inv] using
    congrArg (fun x : GL (Fin 2) ℝ ↦ (⇑F ∣[k] x⁻¹) τ) (mapGL_equivMapOfInjective_symm q.out).symm

variable (N k) in
/-- **The trace from `Γ₁(N)` to `Γ₀(N)`**, Mathlib's `CuspForm.trace`, as a `ℂ`-linear map. By
`coe_trace_eq_sum_diamondOpCusp` it is the diamond sum `F ↦ ∑ᵤ ⟨u⟩ F`. -/
noncomputable def cuspFormTraceGamma0 [NeZero N] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun F := CuspForm.trace ((Gamma0 N).map (mapGL ℝ)) F
  map_add' F G := by
    apply DFunLike.coe_injective
    simp only [FunLike.coe_add]
    rw [coe_trace_eq_sum_diamondOpCusp (F + G), coe_trace_eq_sum_diamondOpCusp F,
      coe_trace_eq_sum_diamondOpCusp G]
    simp only [map_add]
    rw [Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    apply DFunLike.coe_injective
    simp only [FunLike.coe_smul]
    rw [coe_trace_eq_sum_diamondOpCusp (c • F), coe_trace_eq_sum_diamondOpCusp F]
    simp only [map_smul]
    rw [← Finset.smul_sum]
    rfl

/-- `cuspFormTraceGamma0` is Mathlib's `CuspForm.trace`. -/
theorem cuspFormTraceGamma0_apply [NeZero N] (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    cuspFormTraceGamma0 N k F = CuspForm.trace ((Gamma0 N).map (mapGL ℝ)) F :=
  (rfl)

/-- Tracing the restriction of a `Γ₀(N)` cusp form multiplies it by the index
`#(ZMod N)ˣ`. -/
@[simp]
theorem cuspFormTraceGamma0_ofLe [NeZero N]
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspFormTraceGamma0 N k (CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f) =
      (Fintype.card (ZMod N)ˣ : ℂ) • f := by
  apply DFunLike.coe_injective
  ext τ
  rw [cuspFormTraceGamma0_apply, coe_trace_eq_sum_diamondOpCusp]
  simp [diamondOpCusp_ofLe]

/-- Tracing a level-raised cusp form commutes with level raising when the diamond sum at the
lower level is the restriction of a `Γ₀(M)` cusp form. -/
theorem cuspFormTraceGamma0_levelRaise {M d : ℕ} [NeZero N] [NeZero d]
    (hMN : M ∣ N) (hdvd : d * M ∣ N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (g₀ : CuspForm ((Gamma0 M).map (mapGL ℝ)) k)
    (hsum : CuspForm.ofLe (Gamma1_map_le_Gamma0_map M) g₀ =
      ∑ u : (ZMod N)ˣ, diamondOpCusp k (ZMod.unitsMap hMN u) g) :
    cuspFormTraceGamma0 N k
        (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g) =
      CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd hdvd) g₀ := by
  apply DFunLike.coe_injective
  rw [cuspFormTraceGamma0_apply, coe_trace_eq_sum_diamondOpCusp]
  simp_rw [CuspForm.diamondOpCusp_levelRaise hdvd, ← CuspForm.levelRaiseₗ_apply, ← map_sum,
    CuspForm.levelRaiseₗ_apply, ← hsum]
  ext τ
  simp

end Trace

end TauCeti
