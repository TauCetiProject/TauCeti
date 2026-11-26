/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Automorphism
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.QExpansion
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Degree

/-!
# Automorphisms of `ℂ` acting on the Fourier coefficients of modular functions of level `N`

Let `ℂ(X(N))` be the field of meromorphic functions on the compactified modular curve `X(N)`, and
expand its elements at the cusp `∞` in `q = exp (2πiτ / N)`. For a ring automorphism `σ` of `ℂ`
and `F ∈ ℂ(X(N))`, applying `σ` to every Fourier coefficient of `F` gives the expansion of a
function `F^σ ∈ ℂ(X(N))` (`TauCeti.exists_laurentQExpansion_eq_mapRingHom`), unique by the
`q`-expansion principle. The automorphism `σ` need not be continuous, so `F^σ` is not obtained
from the values of `F`. Its existence comes from the generators of the function field: the
functions with a conjugate expansion form a subfield, which contains the constants, the modular
invariant `j`, whose coefficients are rational, and every Fricke function `f_a`, whose conjugate
is the Fricke function `f_{(a₀, d a₁)}` when `σ (ζ_N) = ζ_N ^ d`
(`TauCeti.map_laurentQExpansion_frickeMeromorphicFunction`). These generate `ℂ(X(N))` over `ℂ`
(`TauCeti.adjoin_insert_image_frickeMeromorphicFunction_eq_top`).

So the automorphism group of `ℂ` acts on `ℂ(X(N))` by ring automorphisms
(`TauCeti.modularFunctionCoeffAction`), semilinearly: `(c F)^σ = σ(c) F^σ`. For a modular form
`f` of level `N` and weight `k ≥ 0`, the quotient `f ^ 12 / Δ ^ k` has weight zero and is an
element of `ℂ(X(N))`, so this action is the starting point for constructing Galois conjugates of
modular forms of level `N` through their Fourier coefficients, following Shimura (see the
reference below). Neither the conjugation of modular forms nor any rationality statement for
their Fourier coefficients is proved in this file.

The action interacts with the rest of the structure as follows.

* **Descent.** A function has its Fourier coefficients in a subfield `K` of `ℂ` exactly when it is
  fixed by every automorphism of `ℂ` over `K`
  (`TauCeti.mem_coeffSubfield_iff_forall_modularFunctionCoeffAction_eq`), because the fixed field
  of all automorphisms of `ℂ` over `K` is `K`. For `K = ℚ(ζ_N)` this exhibits `F_N` as a fixed
  field.
* **Fractional linear maps.** The action of `SL(2, ℤ/Nℤ)` is twisted by the diagonal matrix
  `diag(1, d)`, where `σ (ζ_N) = ζ_N ^ d`: if `g diag(1, d) = diag(1, d) g'`, then
  `(F ∘ g)^σ = F^σ ∘ g'` (`TauCeti.modularFunctionCoeffAction_unop_modularFunctionActionZMod`).
  The expansion of a function at the cusp `g • ∞` is the expansion of its composite with `g` at
  `∞`, so this relates the expansions of `F^σ` at the other cusps to those of `F`.

## Main declarations

* `TauCeti.exists_laurentQExpansion_eq_mapRingHom`: the conjugate expansion of a function on
  `X(N)` by a ring endomorphism of `ℂ` is again an expansion.
* `TauCeti.modularFunctionCoeffAction`: the action of the automorphisms of `ℂ` on `ℂ(X(N))`,
  characterized by `TauCeti.laurentQExpansion_modularFunctionCoeffAction`.
* `TauCeti.modularFunctionCoeffAction_algebraMap`, `TauCeti.modularFunctionCoeffAction_smul`:
  semilinearity.
* `TauCeti.modularFunctionCoeffAction_frickeMeromorphicFunction`: the action on Fricke functions.
* `TauCeti.mem_coeffSubfield_iff_forall_modularFunctionCoeffAction_eq`: descent of coefficients.
* `TauCeti.modularFunctionCoeffAction_unop_modularFunctionActionZMod`: the twisted commutation
  with the action of `SL(2, ℤ/Nℤ)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§6.1–6.2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Matrix MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- The meromorphic functions on `X(N)` whose expansion at `∞`, with `σ` applied to its
coefficients, is again the expansion of a meromorphic function on `X(N)`. -/
private def coeffConjSubfield (σ : ℂ →+* ℂ) :
    Subfield (MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :=
  (laurentQExpansion (cuspDatumInftyGamma N) :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient →+*
        LaurentSeries ℂ).fieldRange.comap
    ((HahnSeries.mapRingHom σ).comp (laurentQExpansion (cuspDatumInftyGamma N) :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient →+* LaurentSeries ℂ))

private theorem mem_coeffConjSubfield {σ : ℂ →+* ℂ}
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    F ∈ coeffConjSubfield σ ↔
      ∃ G, laurentQExpansion (cuspDatumInftyGamma N) G =
        HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  simp [coeffConjSubfield, RingHom.mem_fieldRange]

/-- **Conjugate expansions are expansions.** For every ring endomorphism `σ` of `ℂ` and every
meromorphic function `F` on `X(N)`, applying `σ` to the coefficients of the Laurent expansion of
`F` at `∞` gives the Laurent expansion of a meromorphic function on `X(N)`. -/
theorem exists_laurentQExpansion_eq_mapRingHom (σ : ℂ →+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    ∃ G, laurentQExpansion (cuspDatumInftyGamma N) G =
      HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := N) σ
  refine mem_coeffConjSubfield.mp ((subfield_eq_top_of_frickeMeromorphicFunction_mem (N := N)
    (S := coeffConjSubfield σ) (fun c ↦ ?_) ?_ fun a _ ↦ ?_).symm ▸ Subfield.mem_top F)
  · refine mem_coeffConjSubfield.mpr ⟨algebraMap ℂ _ (σ c), ?_⟩
    simp [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.mapRingHom_single]
  · exact mem_coeffConjSubfield.mpr ⟨_, (mapRingHom_laurentQExpansion_eq_of_mem_coeffSubfield _
      (fun _ hx ↦ hx) (mem_coeffIntermediateField.mp
        (compactifiedQuotientComap_jMeromorphicFunction_mem_coeffIntermediateField N
          (σ.eqLocusField (RingHom.id ℂ))))).symm⟩
  · exact mem_coeffConjSubfield.mpr
      ⟨_, (map_laurentQExpansion_frickeMeromorphicFunction hd a).symm⟩

/-- The function on `X(N)` whose expansion at `∞` is the `σ`-conjugate of that of `F`. -/
private def coeffConj (σ : ℂ →+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient :=
  (exists_laurentQExpansion_eq_mapRingHom σ F).choose

private theorem laurentQExpansion_coeffConj (σ : ℂ →+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    laurentQExpansion (cuspDatumInftyGamma N) (coeffConj σ F) =
      HahnSeries.mapRingHom σ (laurentQExpansion (cuspDatumInftyGamma N) F) :=
  (exists_laurentQExpansion_eq_mapRingHom σ F).choose_spec

/-- Conjugating by `τ` and then by `σ` is conjugating by `σ ∘ τ`. -/
private theorem coeffConj_coeffConj (σ τ : ℂ →+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    coeffConj σ (coeffConj τ F) = coeffConj (σ.comp τ) F :=
  laurentQExpansion_injective _ <| by
    rw [laurentQExpansion_coeffConj, laurentQExpansion_coeffConj, laurentQExpansion_coeffConj,
      HahnSeries.mapRingHom_comp, RingHom.comp_apply]

private theorem coeffConj_id
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    coeffConj (RingHom.id ℂ) F = F :=
  laurentQExpansion_injective _ <| by
    rw [laurentQExpansion_coeffConj, HahnSeries.mapRingHom_id, RingHom.id_apply]

variable (N) in
/-- **The automorphisms of `ℂ` act on the modular functions of level `N` through their Fourier
coefficients.** The automorphism `σ` of `ℂ` sends a meromorphic function `F` on `X(N)` to the
function `F^σ` whose Laurent expansion at `∞`, in `q = exp (2πiτ / N)`, is obtained by applying `σ`
to every coefficient of that of `F` (`TauCeti.laurentQExpansion_modularFunctionCoeffAction`). This
is a left action by ring automorphisms; it is semilinear over `σ`, not `ℂ`-linear. -/
def modularFunctionCoeffAction :
    (ℂ ≃+* ℂ) →* (MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient ≃+*
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) where
  toFun σ :=
    { toFun := coeffConj σ
      invFun := coeffConj σ.symm
      left_inv F := by
        rw [coeffConj_coeffConj, ← RingEquiv.toRingHom_trans, RingEquiv.self_trans_symm,
          RingEquiv.toRingHom_refl, coeffConj_id]
      right_inv F := by
        rw [coeffConj_coeffConj, ← RingEquiv.toRingHom_trans, RingEquiv.symm_trans_self,
          RingEquiv.toRingHom_refl, coeffConj_id]
      map_mul' F G := laurentQExpansion_injective (cuspDatumInftyGamma N) <| by
        simp only [map_mul, laurentQExpansion_coeffConj]
      map_add' F G := laurentQExpansion_injective (cuspDatumInftyGamma N) <| by
        simp only [map_add, laurentQExpansion_coeffConj] }
  map_one' := RingEquiv.ext coeffConj_id
  map_mul' σ τ := RingEquiv.ext fun F ↦ (coeffConj_coeffConj (σ : ℂ →+* ℂ) τ F).symm

private theorem modularFunctionCoeffAction_apply (σ : ℂ ≃+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    modularFunctionCoeffAction N σ F = coeffConj σ F :=
  rfl

/-- **The Fourier coefficients of `F^σ`** are the `σ`-conjugates of those of `F`. -/
@[simp]
theorem laurentQExpansion_modularFunctionCoeffAction (σ : ℂ ≃+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    laurentQExpansion (cuspDatumInftyGamma N) (modularFunctionCoeffAction N σ F) =
      HahnSeries.mapRingHom (σ : ℂ →+* ℂ) (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  rw [modularFunctionCoeffAction_apply, laurentQExpansion_coeffConj]

/-- `F^σ` is the unique meromorphic function on `X(N)` whose expansion at `∞` is the
`σ`-conjugate of that of `F`. -/
theorem modularFunctionCoeffAction_apply_eq_iff {σ : ℂ ≃+* ℂ}
    {F G : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    modularFunctionCoeffAction N σ F = G ↔ laurentQExpansion (cuspDatumInftyGamma N) G =
      HahnSeries.mapRingHom (σ : ℂ →+* ℂ) (laurentQExpansion (cuspDatumInftyGamma N) F) := by
  rw [← laurentQExpansion_modularFunctionCoeffAction, (laurentQExpansion_injective _).eq_iff,
    eq_comm]

/-- Conjugating the coefficients by `σ⁻¹` undoes conjugating them by `σ`. -/
@[simp]
theorem modularFunctionCoeffAction_symm_apply_apply (σ : ℂ ≃+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    modularFunctionCoeffAction N σ.symm (modularFunctionCoeffAction N σ F) = F := by
  rw [modularFunctionCoeffAction_apply, modularFunctionCoeffAction_apply, coeffConj_coeffConj,
    ← RingEquiv.toRingHom_trans, RingEquiv.self_trans_symm, RingEquiv.toRingHom_refl,
    coeffConj_id]

/-- The conjugate of a constant function is the conjugate constant. -/
@[simp]
theorem modularFunctionCoeffAction_algebraMap (σ : ℂ ≃+* ℂ) (c : ℂ) :
    modularFunctionCoeffAction N σ
        (algebraMap ℂ (MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) c) =
      algebraMap ℂ _ (σ c) := by
  rw [modularFunctionCoeffAction_apply_eq_iff]
  simp [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.mapRingHom_single]

/-- **Semilinearity**: `(c F)^σ = σ(c) F^σ`. -/
theorem modularFunctionCoeffAction_smul (σ : ℂ ≃+* ℂ) (c : ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    modularFunctionCoeffAction N σ (c • F) = σ c • modularFunctionCoeffAction N σ F := by
  rw [Algebra.smul_def, map_mul, modularFunctionCoeffAction_algebraMap, ← Algebra.smul_def]

/-- An automorphism of `ℂ` fixing a subfield `K` pointwise fixes every function whose Fourier
coefficients lie in `K`. -/
theorem modularFunctionCoeffAction_eq_self_of_mem_coeffSubfield {K : Subfield ℂ} {σ : ℂ ≃+* ℂ}
    (hσ : ∀ x ∈ K, σ x = x)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ coeffSubfield (cuspDatumInftyGamma N) K) :
    modularFunctionCoeffAction N σ F = F :=
  modularFunctionCoeffAction_apply_eq_iff.mpr
    (mapRingHom_laurentQExpansion_eq_of_mem_coeffSubfield _ hσ hF).symm

/-- The modular invariant `j`, which has rational Fourier coefficients, is fixed by every
automorphism of `ℂ`. -/
@[simp]
theorem modularFunctionCoeffAction_compactifiedQuotientComap_jMeromorphicFunction
    (σ : ℂ ≃+* ℂ) :
    modularFunctionCoeffAction N σ (Subgroup.compactifiedQuotientComap
        (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction) =
      Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction :=
  modularFunctionCoeffAction_eq_self_of_mem_coeffSubfield
    (K := (σ : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)) (fun _ hx ↦ hx)
    (mem_coeffIntermediateField.mp
      (compactifiedQuotientComap_jMeromorphicFunction_mem_coeffIntermediateField N _))

/-- **Conjugating a Fricke function.** If `σ (ζ_N) = ζ_N ^ d`, then `σ` sends the Fricke function
`f_a` to `f_{(a₀, d a₁)}`. -/
theorem modularFunctionCoeffAction_frickeMeromorphicFunction {σ : ℂ ≃+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    (a : Fin 2 → ZMod N) :
    modularFunctionCoeffAction N σ (frickeMeromorphicFunction a) =
      frickeMeromorphicFunction ![a 0, (d : ZMod N) * a 1] :=
  modularFunctionCoeffAction_apply_eq_iff.mpr
    (map_laurentQExpansion_frickeMeromorphicFunction (σ := (σ : ℂ →+* ℂ)) hσ a).symm

/-- **Descent of Fourier coefficients.** A meromorphic function on `X(N)` has its Fourier
coefficients at `∞` in a subfield `K` of `ℂ` if and only if it is fixed by every automorphism of
`ℂ` over `K`. -/
theorem mem_coeffSubfield_iff_forall_modularFunctionCoeffAction_eq {K : Subfield ℂ}
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    F ∈ coeffSubfield (cuspDatumInftyGamma N) K ↔
      ∀ σ : ℂ ≃ₐ[K] ℂ, modularFunctionCoeffAction N σ.toRingEquiv F = F := by
  refine ⟨fun hF σ ↦ modularFunctionCoeffAction_eq_self_of_mem_coeffSubfield
    (fun x hx ↦ σ.commutes ⟨x, hx⟩) hF, fun h ↦ (mem_coeffSubfield _).mpr fun n ↦ ?_⟩
  obtain ⟨c, hc⟩ := (TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed (K := K)
    ((laurentQExpansion (cuspDatumInftyGamma N) F).coeff n)).mpr fun σ ↦ by
      simpa using congrArg (HahnSeries.coeff · n)
        (modularFunctionCoeffAction_apply_eq_iff.mp (h σ)).symm
  rw [← hc]
  exact c.property

/-- **Twisted commutation with fractional linear maps.** Let `σ (ζ_N) = ζ_N ^ d`. If
`g, g' ∈ SL(2, ℤ/Nℤ)` satisfy `g diag(1, d) = diag(1, d) g'`, then `(F ∘ g)^σ = F^σ ∘ g'` for
every meromorphic function `F` on `X(N)`. -/
theorem modularFunctionCoeffAction_unop_modularFunctionActionZMod {σ : ℂ ≃+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N))
    {g g' : SL(2, ZMod N)}
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod N)) * Matrix.diagonal ![1, (d : ZMod N)] =
      Matrix.diagonal ![1, (d : ZMod N)] * g')
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    modularFunctionCoeffAction N σ (unop (modularFunctionActionZMod N g) F) =
      unop (modularFunctionActionZMod N g') (modularFunctionCoeffAction N σ F) := by
  let φ := (modularFunctionCoeffAction N σ).toRingHom.comp
    (unop (modularFunctionActionZMod N g)).toRingEquiv.toRingHom
  let ψ := (unop (modularFunctionActionZMod N g')).toRingEquiv.toRingHom.comp
    (modularFunctionCoeffAction N σ).toRingHom
  have hd₁ (b : Fin 2 → ZMod N) : b ᵥ* Matrix.diagonal ![1, (d : ZMod N)] = ![b 0, d * b 1] := by
    rw [Matrix.vecMul_diagonal_vec2, mul_one, mul_comm]
  have h : φ.eqLocusField ψ = ⊤ := by
    refine subfield_eq_top_of_frickeMeromorphicFunction_mem (fun c ↦ ?_) ?_ fun a _ ↦ ?_ <;>
      simp only [RingHom.mem_eqLocusField, φ, ψ, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
    · simp
    · simp
    · rw [unop_modularFunctionActionZMod_frickeMeromorphicFunction,
        modularFunctionCoeffAction_frickeMeromorphicFunction hσ,
        modularFunctionCoeffAction_frickeMeromorphicFunction hσ,
        unop_modularFunctionActionZMod_frickeMeromorphicFunction, ← hd₁, ← hd₁,
        Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hg]
  exact (h.symm ▸ Subfield.mem_top F : F ∈ φ.eqLocusField ψ)

end TauCeti
