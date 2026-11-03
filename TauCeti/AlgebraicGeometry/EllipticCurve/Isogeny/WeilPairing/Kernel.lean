/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective

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

/-- A point killed by an isogeny is killed by its degree. -/
theorem nsmul_eq_zero_of_mem_ker_pointMapHom {P : W₁.Point}
    (hP : P ∈ (Hom.ofIsogeny φ).pointMapHom.ker) : φ.degree • P = 0 := by
  rw [← φ.pointMap_dual_pointMap,
    ← Hom.pointMapHom_apply (Hom.ofIsogeny φ) P, AddMonoidHom.mem_ker.mp hP]
  exact (Hom.ofIsogeny φ.dual).pointMap_zero

/-- The inclusion of an isogeny's kernel in the torsion subgroup at its degree. -/
def kernelToDegreeTorsion : (Hom.ofIsogeny φ).pointMapHom.ker →+
    Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ) where
  toFun P := ⟨P, by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact φ.nsmul_eq_zero_of_mem_ker_pointMapHom P.property⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Inclusion in degree torsion does not change the underlying point. -/
@[simp]
theorem coe_kernelToDegreeTorsion (P : (Hom.ofIsogeny φ).pointMapHom.ker) :
    (φ.kernelToDegreeTorsion P : W₁.Point) = P :=
  (rfl)

/-- The map from the kernel to degree torsion is injective. -/
theorem kernelToDegreeTorsion_injective : Function.Injective φ.kernelToDegreeTorsion := by
  intro P Q h
  exact Subtype.ext (congrArg
    (fun R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ) ↦ (R : W₁.Point)) h)

/-- The map from degree torsion to the dual kernel, `R ↦ φ R`. -/
def degreeTorsionToDualKernel :
    Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ) →+
      (Hom.ofIsogeny φ.dual).pointMapHom.ker where
  toFun R := ⟨(Hom.ofIsogeny φ).pointMap R, by
    rw [AddMonoidHom.mem_ker, Hom.pointMapHom_apply, φ.pointMap_dual_pointMap]
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using R.property⟩
  map_zero' := Subtype.ext ((Hom.ofIsogeny φ).pointMap_zero)
  map_add' R S := Subtype.ext ((Hom.ofIsogeny φ).pointMap_add R S)

/-- The map to the dual kernel is the original isogeny on underlying points. -/
@[simp]
theorem coe_degreeTorsionToDualKernel (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    (φ.degreeTorsionToDualKernel R : W₂.Point) = (Hom.ofIsogeny φ).pointMap R :=
  (rfl)

/-- The kernel of the map from degree torsion consists exactly of the points killed by `φ`. -/
@[simp]
theorem degreeTorsionToDualKernel_eq_zero_iff
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    φ.degreeTorsionToDualKernel R = 0 ↔ (Hom.ofIsogeny φ).pointMap R = 0 :=
  Subtype.ext_iff

/-- The image of the kernel inclusion is exactly the degree-torsion points killed by `φ`.
Together with `degreeTorsionToDualKernel_eq_zero_iff`, this expresses exactness at degree
torsion. -/
theorem mem_range_kernelToDegreeTorsion_iff
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    R ∈ φ.kernelToDegreeTorsion.range ↔ (Hom.ofIsogeny φ).pointMap R = 0 := by
  constructor
  · rintro ⟨P, rfl⟩
    simpa only [coe_kernelToDegreeTorsion, Hom.pointMapHom_apply] using
      AddMonoidHom.mem_ker.mp P.property
  · intro hR
    refine ⟨⟨R, by rwa [AddMonoidHom.mem_ker, Hom.pointMapHom_apply]⟩, ?_⟩
    exact Subtype.ext (φ.coe_kernelToDegreeTorsion _)

local instance : NeZero φ.degree := ⟨φ.degree_ne_zero⟩

variable [IsSepClosed F] (hd : (φ.degree : F) ≠ 0)

include hd in
/-- Every point of the dual kernel is the image under `φ` of a degree-torsion point. -/
theorem degreeTorsionToDualKernel_surjective : Function.Surjective φ.degreeTorsionToDualKernel := by
  intro Q
  obtain ⟨R, hR⟩ := W₂.nsmul_surjective hd (Q : W₂.Point)
  dsimp only at hR
  refine ⟨⟨(Hom.ofIsogeny φ.dual).pointMap R, ?_⟩, Subtype.ext ?_⟩
  · rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← Hom.pointMap_nsmul, hR]
    simpa only [Hom.pointMapHom_apply] using AddMonoidHom.mem_ker.mp Q.property
  · exact (φ.pointMap_pointMap_dual R).trans hR

/-- The kernel of an isogeny is isotropic for the Weil pairing at its degree. -/
theorem weilPairing_eq_zero_of_mem_ker
    {P R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)}
    (hP : (Hom.ofIsogeny φ).pointMap P = 0)
    (hR : (Hom.ofIsogeny φ).pointMap R = 0) :
    weilPairing W₁ φ.degree hd P R = 0 := by
  -- Apply the same surjectivity theorem to the dual, reading equality on underlying points.
  have lifts : ∀ P : (Hom.ofIsogeny φ).pointMapHom.ker,
      ∃ S : Submodule.torsionBy ℤ W₂.Point (φ.degree : ℤ),
        (Hom.ofIsogeny φ.dual).pointMap S = P := by
    have hs := φ.dual.degreeTorsionToDualKernel_surjective
      (by simpa only [degree_dual] using hd)
    simp only [Function.Surjective, Subtype.ext_iff, coe_degreeTorsionToDualKernel] at hs
    rw [φ.degree_dual, φ.dual_dual] at hs
    exact hs
  obtain ⟨S, hS⟩ := lifts ⟨P, by rwa [AddMonoidHom.mem_ker, Hom.pointMapHom_apply]⟩
  have h := φ.weilPairing_eq_weilPairing_dual φ.degree hd
    (S := R) (T := S) (S' := 0) (T' := P) hR hS
  have hz : weilPairing W₁ φ.degree hd R P = 0 := by
    simpa only [map_zero, AddMonoidHom.zero_apply] using h.symm
  rw [← neg_weilPairing, hz, neg_zero]

/-- **The isogeny Weil pairing** on the kernels of `φ` and `φ̂`. It is characterized by
`e_φ(P, φ R) = e_n(P, R)` on degree torsion, where `n = deg φ`. -/
def kernelWeilPairing : (Hom.ofIsogeny φ).pointMapHom.ker →+
    (Hom.ofIsogeny φ.dual).pointMapHom.ker →+ Additive (rootsOfUnity φ.degree F) := by
  let pairing := (weilPairing W₁ φ.degree hd).comp φ.kernelToDegreeTorsion
  let vanishing (P : (Hom.ofIsogeny φ).pointMapHom.ker) :
      φ.degreeTorsionToDualKernel.ker ≤ (pairing P).ker := fun R hR ↦
    φ.weilPairing_eq_zero_of_mem_ker hd
      (by simpa only [coe_kernelToDegreeTorsion, Hom.pointMapHom_apply] using
        AddMonoidHom.mem_ker.mp P.property)
      ((φ.degreeTorsionToDualKernel_eq_zero_iff R).mp hR)
  let lift := φ.degreeTorsionToDualKernel.liftOfSurjective
    (G₃ := Additive (rootsOfUnity φ.degree F)) (φ.degreeTorsionToDualKernel_surjective hd)
  refine { toFun := fun P ↦ lift ⟨pairing P, vanishing P⟩
           map_zero' := ?_
           map_add' := ?_ }
  · ext Q
    obtain ⟨R, rfl⟩ := φ.degreeTorsionToDualKernel_surjective hd Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      map_zero, AddMonoidHom.zero_apply]
  · intro P P'
    ext Q
    obtain ⟨R, rfl⟩ := φ.degreeTorsionToDualKernel_surjective hd Q
    simp only [lift, AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      map_add, AddMonoidHom.add_apply]

/-- The characteristic formula for the kernel pairing, without choosing a lift. -/
@[simp]
theorem kernelWeilPairing_degreeTorsionToDualKernel
    (P : (Hom.ofIsogeny φ).pointMapHom.ker)
    (R : Submodule.torsionBy ℤ W₁.Point (φ.degree : ℤ)) :
    φ.kernelWeilPairing hd P (φ.degreeTorsionToDualKernel R) =
      weilPairing W₁ φ.degree hd (φ.kernelToDegreeTorsion P) R := by
  simp only [kernelWeilPairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
    AddMonoidHom.comp_apply]

/-- The characteristic formula determines the bilinear kernel pairing uniquely. -/
theorem kernelWeilPairing_unique
    (e : (Hom.ofIsogeny φ).pointMapHom.ker →+
      (Hom.ofIsogeny φ.dual).pointMapHom.ker →+ Additive (rootsOfUnity φ.degree F))
    (he : ∀ P R, e P (φ.degreeTorsionToDualKernel R) =
      weilPairing W₁ φ.degree hd (φ.kernelToDegreeTorsion P) R) :
    e = φ.kernelWeilPairing hd := by
  apply AddMonoidHom.ext
  intro P
  apply AddMonoidHom.ext
  intro Q
  obtain ⟨R, rfl⟩ := φ.degreeTorsionToDualKernel_surjective hd Q
  exact (he P R).trans (φ.kernelWeilPairing_degreeTorsionToDualKernel hd P R).symm

/-- The isogeny Weil pairing is nondegenerate in its first argument. -/
theorem kernelWeilPairing_nondegenerate_left
    {P : (Hom.ofIsogeny φ).pointMapHom.ker}
    (hP : ∀ Q, φ.kernelWeilPairing hd P Q = 0) : P = 0 := by
  have h := weilPairing_nondegenerate W₁ φ.degree hd
    (fun R ↦ (φ.kernelWeilPairing_degreeTorsionToDualKernel hd P R).symm.trans
      (hP (φ.degreeTorsionToDualKernel R)))
  exact φ.kernelToDegreeTorsion_injective (h.trans (map_zero φ.kernelToDegreeTorsion).symm)

/-- The isogeny Weil pairing is nondegenerate in its second argument. -/
theorem kernelWeilPairing_nondegenerate_right
    {Q : (Hom.ofIsogeny φ.dual).pointMapHom.ker}
    (hQ : ∀ P, φ.kernelWeilPairing hd P Q = 0) : Q = 0 := by
  obtain ⟨R, rfl⟩ := φ.degreeTorsionToDualKernel_surjective hd Q
  let T : Submodule.torsionBy ℤ W₂.Point (φ.degree : ℤ) :=
    ⟨(Hom.ofIsogeny φ).pointMap R, by
      rw [Submodule.mem_torsionBy_iff, ← Hom.pointMap_zsmul,
        (Submodule.mem_torsionBy_iff _ _).mp R.property]
      exact (Hom.ofIsogeny φ).pointMap_zero⟩
  have hT : T = 0 := weilPairing_nondegenerate W₂ φ.degree hd fun S ↦ by
    let P : (Hom.ofIsogeny φ).pointMapHom.ker :=
      ⟨(Hom.ofIsogeny φ.dual).pointMap S, by
        rw [AddMonoidHom.mem_ker, Hom.pointMapHom_apply, φ.pointMap_pointMap_dual]
        simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using S.property⟩
    have h := φ.weilPairing_eq_weilPairing_dual φ.degree hd
      (S := R) (T := S) (S' := T)
      (T' := φ.kernelToDegreeTorsion P) rfl (by rw [coe_kernelToDegreeTorsion])
    have hz : weilPairing W₁ φ.degree hd (φ.kernelToDegreeTorsion P) R = 0 :=
      (φ.kernelWeilPairing_degreeTorsionToDualKernel hd P R).symm.trans (hQ P)
    rw [← neg_weilPairing W₁, hz, neg_zero] at h
    exact h
  exact Subtype.ext (congrArg
    (fun S : Submodule.torsionBy ℤ W₂.Point (φ.degree : ℤ) ↦ (S : W₂.Point)) hT)

end TauCeti.Isogeny
