/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.CoeffAction
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Action
public import TauCeti.Analysis.Complex.RootsOfUnity.Automorphism

/-!
# The action of `diag(1, d)` on the modular function field `F_N`

Every element `F` of the field `F_N` of modular functions of level `N` has its Laurent expansion
at `∞`, in `q = exp (2πiτ / N)`, with coefficients in `ℚ(ζ_N)`, where `ζ_N = exp (2πi / N)`. For a
unit `d` modulo `N`, applying the automorphism `ζ_N ↦ ζ_N^d` of `ℚ(ζ_N)` to these coefficients
gives the expansion of another element of `F_N`. This constructs the diagonal subgroup action
(`TauCeti.modularFunctionFieldDiagAction`). We compute its joint fixed points with the separate
`SL(2, ℤ/Nℤ)` right action.

The coefficient automorphism is the restriction to `ℚ(ζ_N)` of any field endomorphism `σ` of `ℂ`
with `σ ζ_N = ζ_N^d`. Such a `σ` exists (`Units.exists_ringEquiv_apply_stdAddChar_one`), and its
restriction depends only on `d`. We restrict the coefficient action
`TauCeti.modularFunctionCoeffAction` on `ℂ(X(N))` to `F_N`; its Laurent coefficients remain in
`ℚ(ζ_N)`. The generator formulas and rational fixed points follow from the upstream Fricke
and coefficient descent lemmas.

An element of `F_N` is fixed by every `diag(1, d)` exactly when its expansion has rational
coefficients, because the field fixed by all automorphisms of `ℂ` is `ℚ` and every automorphism
of `ℂ` sends `ζ_N` to some `ζ_N^d`. Together with the fixed field `ℚ(ζ_N)(j)` of `SL(2, ℤ/Nℤ)`,
the joint fixed points of these two separate actions are exactly the level-one field
`F₁ = ℚ(j)`.

## Main declarations

* `TauCeti.modularFunctionFieldDiagAction`: the action of `(ℤ/Nℤ)ˣ` on `F_N` by `diag(1, d)`.
* `TauCeti.laurentQExpansion_modularFunctionFieldDiagAction`: `diag(1, d)` applies to every
  Laurent coefficient a field endomorphism `σ` of `ℂ` with `σ ζ_N = ζ_N^d`.
* `TauCeti.modularFunctionFieldDiagAction_modularFunctionFieldConst`,
  `TauCeti.modularFunctionFieldDiagAction_modularFunctionFieldMapOfLevelOne` and
  `TauCeti.modularFunctionFieldDiagAction_frickeModularFunction`: the action on the generators.
* `TauCeti.modularFunctionFieldDiagAction_injective`: the action is faithful.
* `TauCeti.forall_modularFunctionFieldDiagAction_apply_eq_iff`: the fixed elements are those with
  rational Laurent coefficients.
* `TauCeti.mem_fieldRange_modularFunctionFieldMapOfLevelOne_iff`: the elements fixed by
  `SL(2, ℤ/Nℤ)` and by every `diag(1, d)` form the level-one field `ℚ(j)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient
open TauCeti.RiemannSurface
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- The coefficient action preserves the arithmetic subfield `F_N`. -/
private theorem modularFunctionCoeffAction_mem_modularFunctionField (σ : ℂ ≃+* ℂ)
    (F : modularFunctionField N) : modularFunctionCoeffAction N σ F ∈ modularFunctionField N := by
  obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := N) σ
  rw [mem_modularFunctionField, laurentQExpansion_modularFunctionCoeffAction]
  intro n
  rw [HahnSeries.coeff_mapRingHom]
  rw [← d.coe_cyclotomicConjugate hd ⟨_, mem_modularFunctionField.mp F.property n⟩]
  exact (d.cyclotomicConjugate ⟨_, mem_modularFunctionField.mp F.property n⟩).property

/-- Restriction of the coefficient action to the arithmetic subfield. -/
private def coeffActionRestrict (σ : ℂ ≃+* ℂ) :
    modularFunctionField N ≃+* modularFunctionField N :=
  (modularFunctionCoeffAction N σ).restrict _ _ fun F ↦
    ⟨fun hF ↦ modularFunctionCoeffAction_mem_modularFunctionField σ ⟨F, hF⟩, fun hF ↦ by
      have h := modularFunctionCoeffAction_mem_modularFunctionField σ.symm ⟨_, hF⟩
      have hσ : σ.symm * σ = 1 := RingEquiv.ext σ.symm_apply_apply
      rwa [← RingAut.mul_apply, ← map_mul, hσ, map_one, RingAut.one_apply] at h⟩

/-- The restriction depends only on the image of the standard primitive root, even when
compared with a coefficient endomorphism that is not surjective. -/
private theorem laurentQExpansion_coeffActionRestrict {σ : ℂ ≃+* ℂ} {τ : ℂ →+* ℂ}
    {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (hτ : τ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (F : modularFunctionField N) :
    laurentQExpansion (cuspDatumInftyGamma N) (coeffActionRestrict σ F) =
      HahnSeries.mapRingHom τ (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  rw [coeffActionRestrict, RingEquiv.restrict_apply_coe,
    laurentQExpansion_modularFunctionCoeffAction]
  ext n
  simp only [HahnSeries.coeff_mapRingHom]
  exact (d.coe_cyclotomicConjugate hσ ⟨_, mem_modularFunctionField.mp F.property n⟩).symm.trans
    (d.coe_cyclotomicConjugate hτ ⟨_, mem_modularFunctionField.mp F.property n⟩)

/-- Equality in `F_N` can be checked on Laurent expansions at infinity. -/
private theorem eq_of_laurentQExpansion_eq {F G : modularFunctionField N}
    (h : laurentQExpansion (cuspDatumInftyGamma N) F =
      laurentQExpansion (cuspDatumInftyGamma N) G) : F = G :=
  Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) h)

/-- A complex lift of the cyclotomic automorphism indexed by a unit. -/
private def diagLift (d : (ZMod N)ˣ) : ℂ ≃+* ℂ :=
  Classical.choose d.exists_ringEquiv_apply_stdAddChar_one

private theorem diagLift_apply (d : (ZMod N)ˣ) :
    (diagLift d : ℂ →+* ℂ) (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N) :=
  Classical.choose_spec d.exists_ringEquiv_apply_stdAddChar_one

variable (N) in
/-- **The action of `diag(1, d)` on `F_N`.** Restrict the coefficient action
`TauCeti.modularFunctionCoeffAction` at an automorphism sending `ζ_N` to `ζ_N^d`.
The restriction is independent of this choice. Since `(ℤ/Nℤ)ˣ` is commutative, the
multiplication order needs no opposite. -/
def modularFunctionFieldDiagAction :
    (ZMod N)ˣ →* (modularFunctionField N ≃+* modularFunctionField N) where
  toFun d := coeffActionRestrict (diagLift d)
  map_one' := RingEquiv.ext fun F ↦ eq_of_laurentQExpansion_eq <| by
    rw [laurentQExpansion_coeffActionRestrict (diagLift_apply 1)
      (τ := RingHom.id ℂ) (by simp), HahnSeries.mapRingHom_id, RingHom.id_apply]
    rfl
  map_mul' d e := RingEquiv.ext fun F ↦ eq_of_laurentQExpansion_eq <| by
    let σ := diagLift d
    let τ := diagLift e
    have hσ := diagLift_apply d
    have hτ := diagLift_apply e
    have hστ : ((σ : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ))
        (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar ((d * e : (ZMod N)ˣ) : ZMod N) := by
      rw [RingHom.comp_apply, hτ, ZMod.map_stdAddChar_of_map_stdAddChar_one hσ, Units.val_mul]
    rw [laurentQExpansion_coeffActionRestrict (diagLift_apply (d * e)) hστ]
    rw [RingAut.mul_apply, laurentQExpansion_coeffActionRestrict hσ hσ,
      laurentQExpansion_coeffActionRestrict hτ hτ, HahnSeries.mapRingHom_comp,
      RingHom.comp_apply]

/-- **`diag(1, d)` acts on Laurent coefficients.** If `σ` is a field endomorphism of `ℂ` with
`σ ζ_N = ζ_N^d`, the Laurent expansion at `∞` of the image of `F` under `diag(1, d)` is the
expansion of `F` with `σ` applied to every coefficient. -/
theorem laurentQExpansion_modularFunctionFieldDiagAction {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (F : modularFunctionField N) :
    laurentQExpansion (cuspDatumInftyGamma N) (modularFunctionFieldDiagAction N d F) =
      HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) :=
  laurentQExpansion_coeffActionRestrict (diagLift_apply d) hσ F

/-- The diagonal action is the restriction of the coefficient action for any complex lift
of the prescribed cyclotomic automorphism. -/
theorem coe_modularFunctionFieldDiagAction_apply {σ : ℂ ≃+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (F : modularFunctionField N) :
    (modularFunctionFieldDiagAction N d F :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
      modularFunctionCoeffAction N σ F := by
  apply laurentQExpansion_injective (cuspDatumInftyGamma N)
  rw [laurentQExpansion_modularFunctionFieldDiagAction (σ := (σ : ℂ →+* ℂ)) hσ,
    laurentQExpansion_modularFunctionCoeffAction]

/-- `diag(1, d)` sends the constant `c ∈ ℚ(ζ_N)` to `σ c`, for any field endomorphism `σ` of `ℂ`
with `σ ζ_N = ζ_N^d`. -/
theorem coe_modularFunctionFieldDiagAction_modularFunctionFieldConst {σ : ℂ →+* ℂ}
    {d : (ZMod N)ˣ} (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    (modularFunctionFieldDiagAction N d (modularFunctionFieldConst N c) :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
        algebraMap ℂ _ (σ c) := by
  rw [coe_modularFunctionFieldDiagAction_apply (σ := diagLift d) (diagLift_apply d),
    coe_modularFunctionFieldConst_apply, modularFunctionCoeffAction_algebraMap]
  exact congrArg (algebraMap ℂ _)
    ((d.coe_cyclotomicConjugate (diagLift_apply d) c).symm.trans (d.coe_cyclotomicConjugate hσ c))

/-- The diagonal action on cyclotomic constants, expressed intrinsically in the coefficient
field and without choosing a complex lift. -/
@[simp]
theorem modularFunctionFieldDiagAction_modularFunctionFieldConst (d : (ZMod N)ˣ)
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    modularFunctionFieldDiagAction N d (modularFunctionFieldConst N c) =
      modularFunctionFieldConst N (d.cyclotomicConjugate c) := by
  apply Subtype.ext
  rw [coe_modularFunctionFieldDiagAction_modularFunctionFieldConst
    (diagLift_apply d), coe_modularFunctionFieldConst_apply,
    d.coe_cyclotomicConjugate (diagLift_apply d)]

/-- `diag(1, d)` fixes every function pulled back from the level-one arithmetic field `ℚ(j)`;
in particular it fixes `j`. -/
@[simp]
theorem modularFunctionFieldDiagAction_modularFunctionFieldMapOfLevelOne (d : (ZMod N)ˣ)
    (F : coeffSubfield ModularGroup.cuspDatumInfty ⊥) :
    modularFunctionFieldDiagAction N d (modularFunctionFieldMapOfLevelOne N F) =
      modularFunctionFieldMapOfLevelOne N F := by
  apply Subtype.ext
  rw [coe_modularFunctionFieldDiagAction_apply (σ := diagLift d) (diagLift_apply d)]
  apply modularFunctionCoeffAction_eq_self_of_mem_coeffSubfield (σ := diagLift d)
    (K := ⊥) (fun _ hx ↦ (bot_le : (⊥ : Subfield ℂ) ≤
      (diagLift d : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)) hx)
  rw [coe_modularFunctionFieldMapOfLevelOne_apply]
  exact (compactifiedQuotientComap_mem_coeffSubfield_iff (D := cuspDatumInftyGamma N) _
    (by simp)).mpr F.property

/-- `diag(1, d)` sends the Fricke function `f_(a₀, a₁)` to `f_(a₀, d a₁)`. -/
@[simp]
theorem modularFunctionFieldDiagAction_frickeModularFunction (d : (ZMod N)ˣ)
    (a : Fin 2 → ZMod N) :
    modularFunctionFieldDiagAction N d (frickeModularFunction a) =
      frickeModularFunction ![a 0, (d : ZMod N) * a 1] := by
  apply Subtype.ext
  rw [coe_modularFunctionFieldDiagAction_apply (σ := diagLift d) (diagLift_apply d),
    coe_frickeModularFunction, coe_frickeModularFunction]
  exact modularFunctionCoeffAction_frickeMeromorphicFunction
    (σ := diagLift d) (diagLift_apply d) a

/-- **The action of `diag(1, d)` is faithful**: only `d = 1` acts trivially, since `diag(1, d)`
sends the constant `ζ_N` to `ζ_N^d`. -/
theorem modularFunctionFieldDiagAction_injective :
    Function.Injective (modularFunctionFieldDiagAction N) := by
  refine (injective_iff_map_eq_one _).mpr fun d hd ↦ ?_
  have hζ : ZMod.stdAddChar (1 : ZMod N) ∈ Subfield.closure {z : ℂ | z ^ N = 1} :=
    Subfield.subset_closure (ZMod.isPrimitiveRoot_stdAddChar_one N).pow_eq_one
  have h := congrArg Subtype.val (DFunLike.congr_fun hd (modularFunctionFieldConst N ⟨_, hζ⟩))
  rw [coe_modularFunctionFieldDiagAction_modularFunctionFieldConst
    (diagLift_apply d), RingAut.one_apply, coe_modularFunctionFieldConst_apply,
    diagLift_apply] at h
  exact Units.val_eq_one.mp (ZMod.injective_stdAddChar ((algebraMap ℂ _).injective h))

/-! ### Fixed fields -/

/-- **The elements fixed by every `diag(1, d)`** are those whose Laurent expansion at `∞` has
rational coefficients. -/
theorem forall_modularFunctionFieldDiagAction_apply_eq_iff {F : modularFunctionField N} :
    (∀ d, modularFunctionFieldDiagAction N d F = F) ↔
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        coeffSubfield (cuspDatumInftyGamma N) ⊥ := by
  rw [mem_coeffSubfield_iff_forall_modularFunctionCoeffAction_eq]
  constructor
  · intro hF σ
    obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := N) σ
    apply laurentQExpansion_injective (cuspDatumInftyGamma N)
    rw [laurentQExpansion_modularFunctionCoeffAction,
      ← laurentQExpansion_modularFunctionFieldDiagAction hd F, hF d]
  · intro hF d
    let σ : ℂ ≃ₐ[(⊥ : Subfield ℂ)] ℂ :=
      { diagLift d with commutes' := fun c ↦ (bot_le : (⊥ : Subfield ℂ) ≤
          (diagLift d : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)) c.property }
    apply Subtype.ext
    rw [coe_modularFunctionFieldDiagAction_apply (σ := diagLift d) (diagLift_apply d)]
    exact hF σ

/-- **The elements fixed by `SL(2, ℤ/Nℤ)` and every `diag(1, d)` form `ℚ(j)`.** An element of
`F_N` is fixed by every `g ∈ SL(2, ℤ/Nℤ)`, acting by fractional linear maps, and by every
`diag(1, d)` exactly when it is pulled back from the level-one field `ℚ(j)`. -/
theorem mem_fieldRange_modularFunctionFieldMapOfLevelOne_iff {F : modularFunctionField N} :
    F ∈ (modularFunctionFieldMapOfLevelOne N).fieldRange ↔
      (∀ g : SL(2, ZMod N), unop (modularFunctionFieldActionZMod N g) F = F) ∧
        ∀ d, modularFunctionFieldDiagAction N d F = F := by
  rw [RingHom.mem_fieldRange]
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨fun g ↦ unop_modularFunctionFieldActionZMod_modularFunctionFieldMapOfLevelOne g G,
      fun d ↦ modularFunctionFieldDiagAction_modularFunctionFieldMapOfLevelOne d G⟩
  · rintro ⟨hSL, hdiag⟩
    obtain ⟨G, hG⟩ := (forall_unop_modularFunctionActionZMod_apply_eq_iff (N := N)).mp fun g ↦ by
      rw [← coe_unop_modularFunctionFieldActionZMod_apply, hSL g]
    have hGbot : G ∈ coeffSubfield ModularGroup.cuspDatumInfty ⊥ :=
      (compactifiedQuotientComap_mem_coeffSubfield_iff (D := cuspDatumInftyGamma N) _
        (by simp)).mp
        (hG ▸ forall_modularFunctionFieldDiagAction_apply_eq_iff.mp hdiag)
    exact ⟨⟨G, hGbot⟩, Subtype.ext (by rw [coe_modularFunctionFieldMapOfLevelOne_apply, hG])⟩

end TauCeti
