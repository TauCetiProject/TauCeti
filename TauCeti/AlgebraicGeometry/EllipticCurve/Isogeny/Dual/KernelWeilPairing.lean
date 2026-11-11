/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

/-!
# The Weil pairing on the kernels of dual isogenies

For an isogeny `φ : W₁ → W₂` of degree `n` invertible in a separably closed field `F`,
there is a nondegenerate bilinear pairing

`ker φ × ker φ̂ → Additive (rootsOfUnity n F)`.

It is characterized by `e_φ(P, φ R) = e_n(P, R)` for `R ∈ W₁[n]`. Every point of
`ker φ̂` has such a lift. The value is independent of the lift because `ker φ` is
isotropic for `e_n`: lift its first argument through `φ̂` and use the adjointness of
`φ` and `φ̂`. This kernel pairing is the coefficient pairing used in the local duality
of isogeny descent, unlike the restriction of `e_n` to `ker φ × ker φ`, which is zero.

The construction uses the native point maps, the existing Weil pairing and its adjointness
under dual isogenies. No choice of bases or cyclicity of either kernel is required.
The maps `kerToTorsion` and `torsionToDualKer` are the native-point counterparts of
`TauCeti.Isogeny.kerCoeffToTorsionCoeff` and `TauCeti.Isogeny.torsionCoeffToDualKerCoeff`;
`TauCeti.Isogeny.torsionShortExact` in
`TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion` packages their
sequence as discrete Galois modules. The pairing is defined on geometric points;
no Galois action is considered.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.8, the isogeny Weil pairing.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂)

variable [IsSepClosed F] (hd : (φ.degree : F) ≠ 0)

/-- The kernel of an isogeny is isotropic for the Weil pairing at its degree. -/
theorem weilPairing_eq_zero_of_pointMap_eq_zero
    {P R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)}
    (hP : (Hom.ofIsogeny φ).pointMap P = 0)
    (hR : (Hom.ofIsogeny φ).pointMap R = 0) :
    weilPairing W₁ φ.degree hd P R = 0 := by
  have := φ.isSeparable_dual_of_degree_ne_zero hd
  obtain ⟨S, hS⟩ := φ.exists_dual_pointMap_eq_of_mem_ker
    ((Hom.mem_ker_pointMapHom_iff _ _).mpr hP)
  have h := φ.weilPairing_eq_weilPairing_dual φ.degree hd
    (S := R) (T := S) (S' := 0) (T' := P) hR hS
  have hz : weilPairing W₁ φ.degree hd R P = 0 := by
    simpa only [map_zero, AddMonoidHom.zero_apply] using h.symm
  rw [← neg_weilPairing, hz, neg_zero]

/-- **The isogeny Weil pairing** on the kernels of `φ` and `φ̂`. It is characterized by
`e_φ(P, φ R) = e_n(P, R)` on degree torsion, where `n = deg φ`. -/
def kerWeilPairing : (Hom.ofIsogeny φ).pointMapHom.ker →+
    (Hom.ofIsogeny φ.dual).pointMapHom.ker →+ Additive (rootsOfUnity φ.degree F) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hd).2
  let pairing := (weilPairing W₁ φ.degree hd).comp φ.kerToTorsion
  let vanishing (P : (Hom.ofIsogeny φ).pointMapHom.ker) :
      φ.torsionToDualKer.ker ≤ (pairing P).ker := fun R hR ↦
    φ.weilPairing_eq_zero_of_pointMap_eq_zero hd
      (φ.pointMap_kerToTorsion P)
      ((φ.torsionToDualKer_eq_zero_iff R).mp hR)
  let lift := φ.torsionToDualKer.liftOfSurjective
    (G₃ := Additive (rootsOfUnity φ.degree F)) φ.torsionToDualKer_surjective
  refine { toFun := fun P ↦ lift ⟨pairing P, vanishing P⟩
           map_zero' := ?_
           map_add' := ?_ }
  · ext Q
    obtain ⟨R, rfl⟩ := φ.torsionToDualKer_surjective Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      map_zero, AddMonoidHom.zero_apply]
  · intro P P'
    ext Q
    obtain ⟨R, rfl⟩ := φ.torsionToDualKer_surjective Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      map_add, AddMonoidHom.add_apply]

/-- The characteristic formula for the kernel pairing, without choosing a lift. -/
@[simp]
theorem kerWeilPairing_torsionToDualKer
    (P : (Hom.ofIsogeny φ).pointMapHom.ker)
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    φ.kerWeilPairing hd P (φ.torsionToDualKer R) =
      weilPairing W₁ φ.degree hd (φ.kerToTorsion P) R := by
  simp only [kerWeilPairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
    AddMonoidHom.comp_apply]

/-- The characteristic formula determines the bilinear kernel pairing uniquely. -/
theorem kerWeilPairing_unique
    (e : (Hom.ofIsogeny φ).pointMapHom.ker →+
      (Hom.ofIsogeny φ.dual).pointMapHom.ker →+ Additive (rootsOfUnity φ.degree F))
    (he : ∀ P R, e P (φ.torsionToDualKer R) =
      weilPairing W₁ φ.degree hd (φ.kerToTorsion P) R) :
    e = φ.kerWeilPairing hd := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hd).2
  apply AddMonoidHom.ext
  intro P
  apply AddMonoidHom.ext
  intro Q
  obtain ⟨R, rfl⟩ := φ.torsionToDualKer_surjective Q
  exact (he P R).trans (φ.kerWeilPairing_torsionToDualKer hd P R).symm

/-- The isogeny Weil pairing is nondegenerate in its first argument. -/
theorem kerWeilPairing_nondegenerate_left
    {P : (Hom.ofIsogeny φ).pointMapHom.ker}
    (hP : ∀ Q, φ.kerWeilPairing hd P Q = 0) : P = 0 := by
  have h := weilPairing_nondegenerate W₁ φ.degree hd
    (fun R ↦ (φ.kerWeilPairing_torsionToDualKer hd P R).symm.trans
      (hP (φ.torsionToDualKer R)))
  exact φ.kerToTorsion_injective (h.trans (map_zero φ.kerToTorsion).symm)

/-- The isogeny Weil pairing is nondegenerate in its second argument. -/
theorem kerWeilPairing_nondegenerate_right
    {Q : (Hom.ofIsogeny φ.dual).pointMapHom.ker}
    (hQ : ∀ P, φ.kerWeilPairing hd P Q = 0) : Q = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hd).2
  obtain ⟨R, rfl⟩ := φ.torsionToDualKer_surjective Q
  let T := torsionByMap _ (Hom.ofIsogeny φ).pointMapHom.toIntLinearMap R
  have hT_coe : (T : W₂.Point) = (Hom.ofIsogeny φ).pointMap R := by
    rw [coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap, Hom.pointMapHom_apply]
  have hT : T = 0 := weilPairing_nondegenerate W₂ φ.degree hd fun S ↦ by
    let P : (Hom.ofIsogeny φ).pointMapHom.ker :=
      ⟨(Hom.ofIsogeny φ.dual).pointMap S, φ.dual_pointMap_mem_ker_pointMapHom S⟩
    have h := φ.weilPairing_eq_weilPairing_dual φ.degree hd
      (S := R) (T := S) (S' := T)
      (T' := φ.kerToTorsion P) hT_coe.symm (by
        -- The underlying point of `P` is the dual image by its local definition.
        rw [coe_kerToTorsion])
    have hz : weilPairing W₁ φ.degree hd (φ.kerToTorsion P) R = 0 :=
      (φ.kerWeilPairing_torsionToDualKer hd P R).symm.trans (hQ P)
    rw [← neg_weilPairing W₁, hz, neg_zero] at h
    exact h
  apply Subtype.ext
  rw [coe_torsionToDualKer, ← hT_coe]
  exact congrArg Subtype.val hT

end TauCeti.Isogeny
