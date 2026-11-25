/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia.Extension
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

/-!
# Restriction of unramified local Galois representations to a finite extension

Let `L/K` be a finite extension of nonarchimedean local fields of residue degree `f = f(L/K)`,
embedded in a separable closure of `K` by `ι`, and let `G_L → G_K` be the resulting continuous
embedding of absolute Galois groups (`TauCeti.continuousAbsoluteGaloisGroupExtend`). A continuous
representation `ρ` of `G_K` restricts to a representation `ρ|_{G_L}` of `G_L`.

Since the inertia subgroup of `L` is the preimage of that of `K`
(`TauCeti.comap_absoluteGaloisGroupExtend_inertiaSubgroup`), the restriction of an unramified
representation is unramified, and likewise for tame ramification; when `L/K` is unramified the
two inertia subgroups agree and the converse holds. An arithmetic Frobenius lift of `L` acts on the
maximal unramified extension of `K` as the `f`-th power of the arithmetic Frobenius of `K`, so on an
unramified `ρ` it acts as `ρ(Φ_K)^f`. Hence the Frobenius polynomial of the restriction is the
characteristic polynomial of `ρ(Φ_K)^f`, and the geometric one that of `ρ(Φ_K⁻¹)^f`.

## Main declarations

All names are in the namespace `TauCeti.ContinuousRep`.

* `IsUnramified.res_continuousAbsoluteGaloisGroupExtend`,
  `IsTamelyRamified.res_continuousAbsoluteGaloisGroupExtend`: restriction preserves
  unramifiedness and tame ramification;
  `isUnramified_res_continuousAbsoluteGaloisGroupExtend_iff_of_ramificationIndex_eq_one` is the
  converse along an unramified extension.
* `IsUnramified.res_continuousAbsoluteGaloisGroupExtend_apply_of_isArithFrobeniusLift`: an
  arithmetic Frobenius lift of `L` acts on `ρ|_{G_L}` as `ρ(Φ_K)^f`.
* `IsUnramified.frobCharpoly_res_continuousAbsoluteGaloisGroupExtend`,
  `IsUnramified.frobCharpolyGeom_res_continuousAbsoluteGaloisGroupExtend`: the Frobenius
  polynomials of the restriction are the characteristic polynomials of `ρ(Φ_K)^f` and
  `ρ(Φ_K⁻¹)^f`.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

namespace ContinuousRep

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}

variable (ι : L →ₐ[K] SeparableClosure K)

/-- **Restriction to a finite extension preserves unramifiedness**, since the inertia subgroup of
`L` maps into that of `K`. -/
theorem IsUnramified.res_continuousAbsoluteGaloisGroupExtend (h : ρ.IsUnramified) :
    (ρ.res (continuousAbsoluteGaloisGroupExtend K L ι)).IsUnramified :=
  isUnramified_iff.2 fun τ hτ ↦ by
    rw [res_apply, continuousAbsoluteGaloisGroupExtend_apply]
    exact isUnramified_iff.1 h _ ((absoluteGaloisGroupExtend_mem_inertiaSubgroup_iff ι).2 hτ)

/-- **Restriction to a finite extension preserves tame ramification**, since the wild inertia
subgroup of `L` maps into that of `K`. -/
theorem IsTamelyRamified.res_continuousAbsoluteGaloisGroupExtend (h : ρ.IsTamelyRamified) :
    (ρ.res (continuousAbsoluteGaloisGroupExtend K L ι)).IsTamelyRamified :=
  isTamelyRamified_iff.2 fun τ hτ ↦ by
    rw [res_apply, continuousAbsoluteGaloisGroupExtend_apply]
    exact isTamelyRamified_iff.1 h _
      ((absoluteGaloisGroupExtend_mem_wildInertiaSubgroup_iff ι).2 hτ)

/-- **Restriction to an unramified extension detects unramifiedness.** If `e(L/K) = 1`, the
inertia subgroup of `K` is the image of that of `L`, so `ρ` is unramified exactly when its
restriction to `G_L` is. -/
theorem isUnramified_res_continuousAbsoluteGaloisGroupExtend_iff_of_ramificationIndex_eq_one
    (he : ramificationIndex K L = 1) :
    (ρ.res (continuousAbsoluteGaloisGroupExtend K L ι)).IsUnramified ↔ ρ.IsUnramified := by
  refine ⟨fun h ↦ isUnramified_iff.2 fun σ hσ ↦ ?_,
    fun h ↦ h.res_continuousAbsoluteGaloisGroupExtend ι⟩
  rw [← map_absoluteGaloisGroupExtend_inertiaSubgroup_of_ramificationIndex_eq_one ι he] at hσ
  obtain ⟨τ, hτ, rfl⟩ := hσ
  simpa using isUnramified_iff.1 h τ hτ

/-- **Frobenius of the restriction to residue degree `f`.** An arithmetic Frobenius lift `τ` of
`L` acts on the restriction of an unramified representation as `ρ(Φ_K)^f`, where `f = f(L/K)`
and `Φ_K` is the chosen arithmetic Frobenius lift of `K`. -/
theorem IsUnramified.res_continuousAbsoluteGaloisGroupExtend_apply_of_isArithFrobeniusLift
    (h : ρ.IsUnramified) {τ : Field.absoluteGaloisGroup L} (hτ : IsArithFrobeniusLift L τ) :
    ρ.res (continuousAbsoluteGaloisGroupExtend K L ι) τ =
      ρ (arithFrobLift K) ^ inertiaDegree K L := by
  rw [res_apply]
  refine h.apply_eq_pow_of_restrictMaximalUnramifiedHom_eq_pow ?_
  rw [continuousAbsoluteGaloisGroupExtend_apply,
    hτ.restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend ι,
    isArithFrobeniusLift_def.1 (isArithFrobeniusLift_arithFrobLift K)]

/-- **Geometric Frobenius of the restriction to residue degree `f`.** The inverse of an
arithmetic Frobenius lift `τ` of `L` acts on the restriction of an unramified representation as
`ρ(Φ_K⁻¹)^f`, where `f = f(L/K)`. -/
theorem IsUnramified.res_continuousAbsoluteGaloisGroupExtend_apply_inv_of_isArithFrobeniusLift
    (h : ρ.IsUnramified) {τ : Field.absoluteGaloisGroup L} (hτ : IsArithFrobeniusLift L τ) :
    ρ.res (continuousAbsoluteGaloisGroupExtend K L ι) τ⁻¹ =
      ρ (arithFrobLift K)⁻¹ ^ inertiaDegree K L := by
  rw [res_apply]
  refine h.apply_eq_pow_of_restrictMaximalUnramifiedHom_eq_pow ?_
  rw [continuousAbsoluteGaloisGroupExtend_apply, map_inv, map_inv, map_inv,
    hτ.restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend ι,
    isArithFrobeniusLift_def.1 (isArithFrobeniusLift_arithFrobLift K), inv_pow]

section FrobCharpoly

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [Module.Free A M] [Module.Finite A M] {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}

/-- **Frobenius polynomial of the restriction to residue degree `f`.** For `ρ` unramified, the
Frobenius polynomial of its restriction to `G_L` is the characteristic polynomial of
`ρ(Φ_K)^f`, where `f = f(L/K)`. -/
theorem IsUnramified.frobCharpoly_res_continuousAbsoluteGaloisGroupExtend (h : ρ.IsUnramified) :
    (ρ.res (continuousAbsoluteGaloisGroupExtend K L ι)).frobCharpoly =
      (ρ (arithFrobLift K) ^ inertiaDegree K L).charpoly := by
  rw [frobCharpoly_def,
    h.res_continuousAbsoluteGaloisGroupExtend_apply_of_isArithFrobeniusLift ι
      (isArithFrobeniusLift_arithFrobLift L)]

/-- **Geometric Frobenius polynomial of the restriction to residue degree `f`.** For `ρ`
unramified, the geometric Frobenius polynomial of its restriction to `G_L` is the characteristic
polynomial of `ρ(Φ_K⁻¹)^f`, where `f = f(L/K)`. -/
theorem IsUnramified.frobCharpolyGeom_res_continuousAbsoluteGaloisGroupExtend
    (h : ρ.IsUnramified) :
    (ρ.res (continuousAbsoluteGaloisGroupExtend K L ι)).frobCharpolyGeom =
      (ρ (arithFrobLift K)⁻¹ ^ inertiaDegree K L).charpoly := by
  rw [frobCharpolyGeom_def,
    h.res_continuousAbsoluteGaloisGroupExtend_apply_inv_of_isArithFrobeniusLift ι
      (isArithFrobeniusLift_arithFrobLift L)]

end FrobCharpoly

end ContinuousRep

end TauCeti
