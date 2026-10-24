/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
-- Proof-only: finiteness of the Selmer group with conditions at the finite completions.
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Finite

/-!
# Isogeny invariance of finiteness of the Shafarevich–Tate group

For elliptic curves over a number field, an isogeny induces a map on Shafarevich–Tate groups
with finite kernel. Consequently one group is finite if and only if the other is finite.
Local triviality is imposed at every place, including the real and complex places.

The dual composite kills the kernel by the degree. Degree-torsion in the group defined using
only finite places is already finite: it is a quotient of the finite degree-Selmer group.
The all-place kernel embeds in this finite group, without omitting any archimedean condition.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve ContCohomology GlobalNumberFields IsDedekindDomain
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (τ : ∀ v : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

/-- Over a number field the map on Shafarevich–Tate groups induced by a nonzero morphism
has finite kernel. Local conditions are taken at all finite and infinite places. -/
theorem finite_ker_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (f.shafarevichTateMap τ).ker := by
  classical
  let τf := fun v : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦ τ (.inl v)
  have : NeZero f.degree := ⟨fun h ↦ hf ((degree_eq_zero_iff f).mp h)⟩
  have := W₁.finite_selmerGroup f.degree τf
  have ht : Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τf) f.degree) :=
    Finite.of_surjective (W₁.selmerShaMap τf f.degree)
      (W₁.selmerShaMap_surjective τf (isUnit_iff_ne_zero.mpr
        (Nat.cast_ne_zero.mpr (NeZero.ne f.degree))))
  let j : (f.shafarevichTateMap τ).ker →
      AddSubgroup.torsionBy (W₁.shafarevichTateGroup τf) f.degree := fun c ↦
    ⟨⟨c.1.1, (W₁.mem_shafarevichTateGroup_iff τf).mpr fun v ↦
      (W₁.mem_shafarevichTateGroup_iff τ).mp c.1.2 (.inl v)⟩,
      AddSubgroup.torsionBy.nsmul_iff.mpr (Subtype.ext (by
        have hc : f.degree • c.1 = 0 := AddSubgroup.torsionBy.nsmul_iff.mp
          (f.ker_shafarevichTateMap_le_torsionBy τ c.2)
        have hc' := congrArg (fun z : W₁.shafarevichTateGroup τ ↦
          (z : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff)) hc
        simpa only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] using hc'))⟩
  exact Finite.of_injective j fun c d h ↦
    Subtype.ext (Subtype.ext (congrArg (fun z ↦ z.1.1) h))

/-- Finiteness transfers backwards along a nonzero morphism of elliptic curves over a number
field: its map on Shafarevich–Tate groups has finite kernel. -/
theorem finite_shafarevichTateGroup_of_finite (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    [Finite (W₂.shafarevichTateGroup τ)] : Finite (W₁.shafarevichTateGroup τ) := by
  have := f.finite_ker_shafarevichTateMap τ hf
  exact (f.shafarevichTateMap τ).finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

variable {τ} in
/-- **Isogeny invariance of finiteness of the Shafarevich–Tate group** over a number field,
with local triviality required at every place. -/
theorem finite_shafarevichTateGroup_iff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (W₁.shafarevichTateGroup τ) ↔ Finite (W₂.shafarevichTateGroup τ) := by
  constructor
  · intro h
    have := h
    exact f.dual.finite_shafarevichTateGroup_of_finite τ (dual_eq_zero_iff.not.mpr hf)
  · intro h
    have := h
    exact f.finite_shafarevichTateGroup_of_finite τ hf

end TauCeti.Isogeny.Hom

end
