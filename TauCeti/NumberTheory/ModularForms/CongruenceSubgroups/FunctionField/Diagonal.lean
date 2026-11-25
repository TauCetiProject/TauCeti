/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Action
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.FieldTheory.IsAlgClosed.Automorphism

/-!
# The action of `diag(1, d)` on the modular function field `F_N`

Every element `F` of the field `F_N` of modular functions of level `N` has its Laurent expansion
at `∞`, in `q = exp (2πiτ / N)`, with coefficients in `ℚ(ζ_N)`, where `ζ_N = exp (2πi / N)`. For a
unit `d` modulo `N`, applying the automorphism `ζ_N ↦ ζ_N^d` of `ℚ(ζ_N)` to these coefficients
gives the expansion of another element of `F_N`. This is the action of the matrix `diag(1, d)` of
`GL₂(ℤ/Nℤ)` on `F_N` (`TauCeti.modularFunctionFieldDiagAction`). The matrices `diag(1, d)`
and `SL(2, ℤ/Nℤ)`, which acts on `F_N` by fractional linear maps, generate `GL₂(ℤ/Nℤ)`.

The coefficient automorphism is the restriction to `ℚ(ζ_N)` of any field endomorphism `σ` of `ℂ`
with `σ ζ_N = ζ_N^d`. Such a `σ` exists (`ZMod.exists_ringEquiv_apply_stdAddChar_one`), and its
restriction depends only on `d`. That `F_N` is stable is checked on the generators of `F_N`
(`TauCeti.modularFunctionField_eq_closure`): the constants in `ℚ(ζ_N)` go to their conjugates,
`j` has rational coefficients, and the Fricke function `f_(a₀, a₁)` goes to `f_(a₀, d a₁)`
(`TauCeti.map_laurentQExpansion_frickeMeromorphicFunction`).

An element of `F_N` is fixed by every `diag(1, d)` exactly when its expansion has rational
coefficients, because the field fixed by all automorphisms of `ℂ` is `ℚ` and every automorphism
of `ℂ` sends `ζ_N` to some `ζ_N^d`. Together with the fixed field `ℚ(ζ_N)(j)` of `SL(2, ℤ/Nℤ)`,
the elements of `F_N` fixed by `SL(2, ℤ/Nℤ)` and by every `diag(1, d)`, which together generate
`GL₂(ℤ/Nℤ)`, are exactly the level-one field `F₁ = ℚ(j)`.

## Main declarations

* `TauCeti.modularFunctionFieldDiagAction`: the action of `(ℤ/Nℤ)ˣ` on `F_N` by `diag(1, d)`.
* `TauCeti.laurentQExpansion_modularFunctionFieldDiagAction`: `diag(1, d)` applies to every
  Laurent coefficient a field endomorphism `σ` of `ℂ` with `σ ζ_N = ζ_N^d`.
* `TauCeti.coe_modularFunctionFieldDiagAction_modularFunctionFieldConst`,
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

/-! ### Coefficient maps on `ℚ(ζ_N)` -/

/-- Applying two field endomorphisms of `ℂ` with the same value at `ζ_N` to the Laurent
coefficients of an element of `F_N` gives the same result. -/
private theorem mapRingHom_laurentQExpansion_eq {σ σ' : ℂ →+* ℂ}
    (h : σ (ZMod.stdAddChar (1 : ZMod N)) = σ' (ZMod.stdAddChar (1 : ZMod N)))
    (F : modularFunctionField N) :
    HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) =
      HahnSeries.mapRingHom σ' (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  ext n
  rw [HahnSeries.coeff_mapRingHom, HahnSeries.coeff_mapRingHom]
  -- `σ` and `σ'` agree on the `N`-th roots of unity, the powers of `ζ_N`, so on `ℚ(ζ_N)`
  refine (Subfield.closure_le (t := σ.eqLocusField σ')).mpr (fun z hz ↦ ?_)
    (mem_modularFunctionField.mp F.property n)
  obtain ⟨i, -, rfl⟩ := ZMod.isPrimitiveRoot_stdAddChar_one.eq_pow_of_pow_eq_one hz
  exact RingHom.mem_eqLocusField.mpr (by rw [map_pow, map_pow, h])

/-- Every field endomorphism of `ℂ` fixes a Laurent expansion with rational coefficients. -/
private theorem mapRingHom_laurentQExpansion_of_mem_coeffSubfield_bot (σ : ℂ →+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ coeffSubfield (cuspDatumInftyGamma N) ⊥) :
    HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) =
      laurentQExpansion (cuspDatumInftyGamma N) F := by
  ext n
  rw [HahnSeries.coeff_mapRingHom]
  exact RingHom.mem_eqLocusField.mp
    (bot_le (a := σ.eqLocusField (RingHom.id ℂ)) ((mem_coeffSubfield _).mp hF n))

/-! ### Stability of `F_N` -/

variable (N) in
/-- The Laurent expansion at `∞` of the elements of `F_N`. -/
private def expansion : modularFunctionField N →+* LaurentSeries ℂ :=
  (laurentQExpansion (cuspDatumInftyGamma N)).toRingHom.comp (modularFunctionField N).subtype

private theorem expansion_apply (F : modularFunctionField N) :
    expansion N F = laurentQExpansion (cuspDatumInftyGamma N) F :=
  rfl

/-- If `σ ζ_N = ζ_N^d` for a unit `d`, applying `σ` to the coefficients of the expansion of an
element of `F_N` gives the expansion of an element of `F_N`. It suffices to check this on the
generators of `F_N`. -/
private theorem mapRingHom_mem_fieldRange_expansion {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    {x : LaurentSeries ℂ} (hx : x ∈ (expansion N).fieldRange) :
    HahnSeries.mapRingHom σ x ∈ (expansion N).fieldRange := by
  obtain ⟨F, rfl⟩ := RingHom.mem_fieldRange.mp hx
  refine (Subfield.closure_le (t := ((expansion N).fieldRange.comap
      (HahnSeries.mapRingHom σ)).comap (laurentQExpansion (cuspDatumInftyGamma N)).toRingHom)).mpr
    (fun G hG ↦ ?_) (modularFunctionField_eq_closure.le F.property)
  rw [SetLike.mem_coe, Subfield.mem_comap, Subfield.mem_comap, RingHom.mem_fieldRange]
  rcases hG with ⟨c, rfl⟩ | rfl | ⟨a, -, rfl⟩
  · -- `σ` permutes the `N`-th roots of unity, so it maps `ℚ(ζ_N)` into itself
    have hσc : σ c ∈ Subfield.closure {z : ℂ | z ^ N = 1} := by
      refine (Subfield.closure_le (t := (Subfield.closure {z : ℂ | z ^ N = 1}).comap σ)).mpr
        (fun z hz ↦ Subfield.mem_comap.mpr (Subfield.subset_closure ?_)) c.property
      rw [Set.mem_ofPred_eq] at hz ⊢
      rw [← map_pow, hz, map_one]
    refine ⟨modularFunctionFieldConst N ⟨σ c, hσc⟩, ?_⟩
    rw [expansion_apply, coe_modularFunctionFieldConst_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, IsScalarTower.algebraMap_apply (Subfield.closure {z : ℂ | z ^ N = 1}) ℂ,
      Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
    simp only [AlgHom.commutes, LaurentSeries.algebraMap_apply, HahnSeries.mapRingHom_apply,
      HahnSeries.map_C]
  · refine ⟨⟨_, compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩, ?_⟩
    exact (mapRingHom_laurentQExpansion_of_mem_coeffSubfield_bot σ
      (mem_coeffIntermediateField.mp
        (compactifiedQuotientComap_jMeromorphicFunction_mem_coeffIntermediateField N ⊥))).symm
  · refine ⟨frickeModularFunction ![a 0, (d : ZMod N) * a 1], ?_⟩
    rw [expansion_apply, coe_frickeModularFunction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact (map_laurentQExpansion_frickeMeromorphicFunction hσ a).symm

/-- A field endomorphism of `ℂ` sending `ζ_N` to `ζ_N^d`, chosen once for each unit `d`. -/
private def diagCoeff (d : (ZMod N)ˣ) : ℂ →+* ℂ :=
  (Classical.choose (ZMod.exists_ringEquiv_apply_stdAddChar_one d)).toRingHom

private theorem diagCoeff_apply_stdAddChar_one (d : (ZMod N)ˣ) :
    diagCoeff d (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N) :=
  Classical.choose_spec (ZMod.exists_ringEquiv_apply_stdAddChar_one d)

/-- The ring endomorphism of `F_N` applying `diagCoeff d` to the Laurent coefficients. -/
private def diagHom (d : (ZMod N)ˣ) : modularFunctionField N →+* modularFunctionField N :=
  (expansion N).rangeRestrictFieldEquiv.symm.toRingHom.comp
    (((HahnSeries.mapRingHom (diagCoeff d)).restrict _ _
      fun _ ↦ mapRingHom_mem_fieldRange_expansion (diagCoeff_apply_stdAddChar_one d)).comp
        (expansion N).rangeRestrictField)

private theorem laurentQExpansion_diagHom {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (F : modularFunctionField N) :
    laurentQExpansion (cuspDatumInftyGamma N) (diagHom d F) =
      HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  rw [← expansion_apply, diagHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingHom.rangeRestrictFieldEquiv_apply_symm_apply,
    RingHom.comp_apply, RingHom.coe_restrict_apply, RingHom.coe_rangeRestrictField,
    expansion_apply]
  exact mapRingHom_laurentQExpansion_eq ((diagCoeff_apply_stdAddChar_one d).trans hσ.symm) F

private theorem diagHom_comp (d e : (ZMod N)ˣ) :
    (diagHom d).comp (diagHom e) = diagHom (d * e) := by
  refine RingHom.ext fun F ↦ Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) ?_)
  have hde : ((diagCoeff d).comp (diagCoeff e)) (ZMod.stdAddChar (1 : ZMod N)) =
      ZMod.stdAddChar ((d * e : (ZMod N)ˣ) : ZMod N) := by
    rw [RingHom.comp_apply, diagCoeff_apply_stdAddChar_one,
      ZMod.map_stdAddChar_of_map_stdAddChar_one (diagCoeff_apply_stdAddChar_one d), Units.val_mul]
  rw [RingHom.comp_apply, laurentQExpansion_diagHom (diagCoeff_apply_stdAddChar_one d),
    laurentQExpansion_diagHom (diagCoeff_apply_stdAddChar_one e),
    laurentQExpansion_diagHom hde, HahnSeries.mapRingHom_comp, RingHom.comp_apply]

private theorem diagHom_one : diagHom (1 : (ZMod N)ˣ) = RingHom.id _ := by
  refine RingHom.ext fun F ↦ Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) ?_)
  rw [laurentQExpansion_diagHom (σ := RingHom.id ℂ) (by rw [RingHom.id_apply, Units.val_one]),
    HahnSeries.mapRingHom_id, RingHom.id_apply, RingHom.id_apply]

/-! ### The action of `diag(1, d)` -/

variable (N) in
/-- **The action of `diag(1, d)` on `F_N`.** For a unit `d` modulo `N`, the matrix `diag(1, d)`
acts on `F_N` by applying the automorphism `ζ_N ↦ ζ_N^d` of `ℚ(ζ_N)` to the Laurent coefficients
at `∞` (`TauCeti.laurentQExpansion_modularFunctionFieldDiagAction`). Since `(ℤ/Nℤ)ˣ` is
commutative, the multiplication order needs no opposite. -/
def modularFunctionFieldDiagAction :
    (ZMod N)ˣ →* (modularFunctionField N ≃+* modularFunctionField N) where
  toFun d := RingEquiv.ofRingHom (diagHom d) (diagHom d⁻¹)
    (by rw [diagHom_comp, mul_inv_cancel, diagHom_one])
    (by rw [diagHom_comp, inv_mul_cancel, diagHom_one])
  map_one' := RingEquiv.ext fun F ↦ RingHom.congr_fun diagHom_one F
  map_mul' d e := RingEquiv.ext fun F ↦ (RingHom.congr_fun (diagHom_comp d e) F).symm

/-- **`diag(1, d)` acts on Laurent coefficients.** If `σ` is a field endomorphism of `ℂ` with
`σ ζ_N = ζ_N^d`, the Laurent expansion at `∞` of the image of `F` under `diag(1, d)` is the
expansion of `F` with `σ` applied to every coefficient. -/
theorem laurentQExpansion_modularFunctionFieldDiagAction {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (F : modularFunctionField N) :
    laurentQExpansion (cuspDatumInftyGamma N) (modularFunctionFieldDiagAction N d F) =
      HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) :=
  laurentQExpansion_diagHom hσ F

/-- `diag(1, d)` sends the constant `c ∈ ℚ(ζ_N)` to `σ c`, for any field endomorphism `σ` of `ℂ`
with `σ ζ_N = ζ_N^d`. -/
theorem coe_modularFunctionFieldDiagAction_modularFunctionFieldConst {σ : ℂ →+* ℂ}
    {d : (ZMod N)ˣ} (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    (modularFunctionFieldDiagAction N d (modularFunctionFieldConst N c) :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
        algebraMap ℂ _ (σ c) := by
  apply laurentQExpansion_injective (cuspDatumInftyGamma N)
  rw [laurentQExpansion_modularFunctionFieldDiagAction hσ, coe_modularFunctionFieldConst_apply]
  simp only [AlgHom.commutes, LaurentSeries.algebraMap_apply, HahnSeries.mapRingHom_apply,
    HahnSeries.map_C]

/-- `diag(1, d)` fixes every function pulled back from the level-one arithmetic field `ℚ(j)`;
in particular it fixes `j`. -/
@[simp]
theorem modularFunctionFieldDiagAction_modularFunctionFieldMapOfLevelOne (d : (ZMod N)ˣ)
    (F : coeffSubfield ModularGroup.cuspDatumInfty ⊥) :
    modularFunctionFieldDiagAction N d (modularFunctionFieldMapOfLevelOne N F) =
      modularFunctionFieldMapOfLevelOne N F := by
  refine Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) ?_)
  rw [laurentQExpansion_modularFunctionFieldDiagAction (diagCoeff_apply_stdAddChar_one d),
    coe_modularFunctionFieldMapOfLevelOne_apply]
  exact mapRingHom_laurentQExpansion_of_mem_coeffSubfield_bot _
    ((compactifiedQuotientComap_mem_coeffSubfield_iff _ (by simp)).mpr F.property)

/-- `diag(1, d)` sends the Fricke function `f_(a₀, a₁)` to `f_(a₀, d a₁)`. -/
@[simp]
theorem modularFunctionFieldDiagAction_frickeModularFunction (d : (ZMod N)ˣ)
    (a : Fin 2 → ZMod N) :
    modularFunctionFieldDiagAction N d (frickeModularFunction a) =
      frickeModularFunction ![a 0, (d : ZMod N) * a 1] := by
  refine Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) ?_)
  rw [laurentQExpansion_modularFunctionFieldDiagAction (diagCoeff_apply_stdAddChar_one d),
    coe_frickeModularFunction, coe_frickeModularFunction]
  exact map_laurentQExpansion_frickeMeromorphicFunction (diagCoeff_apply_stdAddChar_one d) a

/-- **The action of `diag(1, d)` is faithful**: only `d = 1` acts trivially, since `diag(1, d)`
sends the constant `ζ_N` to `ζ_N^d`. -/
theorem modularFunctionFieldDiagAction_injective :
    Function.Injective (modularFunctionFieldDiagAction N) := by
  refine (injective_iff_map_eq_one _).mpr fun d hd ↦ ?_
  have hζ : ZMod.stdAddChar (1 : ZMod N) ∈ Subfield.closure {z : ℂ | z ^ N = 1} :=
    Subfield.subset_closure ZMod.isPrimitiveRoot_stdAddChar_one.pow_eq_one
  have h := congrArg Subtype.val (DFunLike.congr_fun hd (modularFunctionFieldConst N ⟨_, hζ⟩))
  rw [coe_modularFunctionFieldDiagAction_modularFunctionFieldConst
    (diagCoeff_apply_stdAddChar_one d), RingAut.one_apply, coe_modularFunctionFieldConst_apply,
    diagCoeff_apply_stdAddChar_one] at h
  exact Units.val_eq_one.mp (ZMod.injective_stdAddChar ((algebraMap ℂ _).injective h))

/-! ### Fixed fields -/

/-- **The elements fixed by every `diag(1, d)`** are those whose Laurent expansion at `∞` has
rational coefficients. -/
theorem forall_modularFunctionFieldDiagAction_apply_eq_iff {F : modularFunctionField N} :
    (∀ d, modularFunctionFieldDiagAction N d F = F) ↔
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        coeffSubfield (cuspDatumInftyGamma N) ⊥ := by
  refine ⟨fun hF ↦ (mem_coeffSubfield _).mpr fun n ↦ ?_, fun hF d ↦ ?_⟩
  · -- a coefficient of `F` is fixed by every automorphism of `ℂ`, so it is rational
    obtain ⟨q, hq⟩ := (TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed (K := ℚ)
      ((laurentQExpansion (cuspDatumInftyGamma N) F).coeff n)).mpr fun τ ↦ by
        obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := N) (τ : ℂ →+* ℂ)
        have h := congrArg (fun G : modularFunctionField N ↦
          (laurentQExpansion (cuspDatumInftyGamma N) G).coeff n) (hF d)
        rwa [laurentQExpansion_modularFunctionFieldDiagAction hd, HahnSeries.coeff_mapRingHom,
          RingHom.coe_coe] at h
    rw [← hq, eq_ratCast]
    exact SubfieldClass.ratCast_mem _ q
  · refine Subtype.ext (laurentQExpansion_injective (cuspDatumInftyGamma N) ?_)
    rw [laurentQExpansion_modularFunctionFieldDiagAction (diagCoeff_apply_stdAddChar_one d)]
    exact mapRingHom_laurentQExpansion_of_mem_coeffSubfield_bot _ hF

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
