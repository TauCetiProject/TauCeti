/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Basic
import TauCeti.Algebra.Group.Pow

/-!
# The quadratic refinement of a symmetric pairing of odd order

On a finite abelian group `A` of odd order `n`, a symmetric pairing `b : A × A → ℚ/ℤ` has exactly
one quadratic refinement, the map

```text
q(x) = ((n + 1) / 2) · b(x, x).
```

Indeed every quadratic map `q` with polar form `b` satisfies `2q(x) = b(x, x)` and `n q(x) = 0`,
so `q(x) = (n + 1) q(x) = ((n + 1) / 2) · b(x, x)`. Consequently a bilinear isometry between finite
quadratic modules of odd order preserves the quadratic maps, and finite quadratic modules of odd
order are classified by their bilinear modules alone.

## Main declarations

* `TauCeti.FiniteBilinearModule.quadraticRefinement`: the quadratic refinement
  `x ↦ ((n + 1) / 2) · b(x, x)` of a finite bilinear module of odd order `n`.
* `TauCeti.FiniteQuadraticModule.quadratic_eq_nsmul_pairing_self_of_odd` and
  `TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`: every finite quadratic module of odd
  order is the quadratic refinement of its bilinear module.
* `TauCeti.FiniteQuadraticModule.map_quadratic_of_odd`,
  `TauCeti.FiniteQuadraticModule.homOfBilinearHomOfOdd`, and
  `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd`: a bilinear morphism or
  isometry out of a finite quadratic module of odd order is a quadratic morphism or isometry.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`: finite quadratic
  modules of odd order are isometric exactly when their bilinear modules are.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti

universe u v w

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u})

/-- **The quadratic refinement of a symmetric pairing of odd order.** On a finite abelian group
of odd order `n`, the quadratic map `x ↦ ((n + 1) / 2) • b(x, x)` has polar form `b`, since
`(n + 1) • b(x, y) = b(x, y)`. It is the only finite quadratic module structure with pairing `b`
(`TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`).

Exposed so that its bilinear module is `A` by definition, and bilinear isometries into or out of
`A` are bilinear isometries of the refinement. -/
@[expose] noncomputable def quadraticRefinement (hA : Odd (Nat.card A)) :
    FiniteQuadraticModule where
  toFiniteBilinearModule := A
  quadratic := LinearMap.BilinMap.toQuadraticMap (((Nat.card A + 1) / 2) • A.toBilin)
  polar_eq_pairing' x y := by
    have hn : Nat.card A • A.pairing x y = 0 := by
      rw [← pairing_nsmul_left, card_nsmul_eq_zero', pairing_zero_left]
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [LinearMap.smul_apply, toBilin_apply]
    rw [A.pairing_comm y x, ← smul_add, ← two_nsmul, nsmul_two_nsmul_of_odd hA hn]

/-- The bilinear module of the quadratic refinement of `A` is `A`. -/
@[simp]
theorem quadraticRefinement_toFiniteBilinearModule (hA : Odd (Nat.card A)) :
    (A.quadraticRefinement hA).toFiniteBilinearModule = A :=
  (rfl)

/-- The quadratic refinement of a pairing `b` on a group of odd order `n` is
`x ↦ ((n + 1) / 2) • b(x, x)`. -/
@[simp]
theorem quadraticRefinement_quadratic (hA : Odd (Nat.card A)) (x : A) :
    (A.quadraticRefinement hA).quadratic x = ((Nat.card A + 1) / 2) • A.pairing x x :=
  (LinearMap.BilinMap.toQuadraticMap_apply _ x).trans <| by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, toBilin_apply]

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- On a finite quadratic module of odd order `n`, the quadratic map is determined by the pairing:
`q(x) = ((n + 1) / 2) • b(x, x)`. -/
theorem quadratic_eq_nsmul_pairing_self_of_odd (hA : Odd (Nat.card A)) (x : A) :
    A.quadratic x = ((Nat.card A + 1) / 2) • A.toFiniteBilinearModule.pairing x x := by
  rw [← polar_eq_pairing, QuadraticMap.polar_self,
    nsmul_two_nsmul_of_odd hA (A.natCard_nsmul_quadratic_of_odd hA x)]

/-- **Uniqueness of the quadratic refinement in odd order.** A finite quadratic module of odd
order is the quadratic refinement of its bilinear module. -/
theorem eq_quadraticRefinement (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    A = A.toFiniteBilinearModule.quadraticRefinement hA := by
  obtain ⟨B, q, hq⟩ := A
  congr 1
  ext x
  exact (quadratic_eq_nsmul_pairing_self_of_odd (A := ⟨B, q, hq⟩) hA x).trans
    (B.quadraticRefinement_quadratic hA x).symm

/-- **Out of an odd-order module, a bilinear morphism is automatically a quadratic morphism.**
No nondegeneracy or codomain cardinality hypothesis is required, and the underlying map is
unchanged. -/
def homOfBilinearHomOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Hom A B where
  toLinearMap := f.toAddMonoidHom.toIntLinearMap
  map_app' x := by
    rw [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap,
      FiniteBilinearModule.Hom.coe_toAddMonoidHom, ← sub_eq_zero]
    refine (nsmul_eq_zero_iff_of_coprime hA.coprime_two_left).mp ⟨?_, ?_⟩
    · rw [nsmul_sub, ← QuadraticMap.polar_self, ← QuadraticMap.polar_self,
        A.polar_eq_pairing, B.polar_eq_pairing, f.map_pairing, sub_self]
    · rw [nsmul_sub,
        B.nsmul_quadratic_of_odd hA (f x) (by rw [← map_nsmul, card_nsmul_eq_zero', map_zero]),
        A.natCard_nsmul_quadratic_of_odd hA, sub_self]

/-- Upgrading a bilinear morphism from an odd-order module preserves the underlying map. -/
@[simp]
theorem homOfBilinearHomOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) (x : A) :
    homOfBilinearHomOfOdd hA f x = f x :=
  (rfl)

/-- Forgetting the quadratic structure after upgrading a bilinear morphism at odd order recovers
the original bilinear morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_toFiniteBilinearModule (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (homOfBilinearHomOfOdd hA f).toFiniteBilinearModule = f := by
  ext x; simp

/-- Upgrading the polar bilinear morphism of a quadratic morphism at odd order recovers the
quadratic morphism. -/
@[simp]
theorem toFiniteBilinearModule_homOfBilinearHomOfOdd (hA : Odd (Nat.card A)) (g : Hom A B) :
    homOfBilinearHomOfOdd hA g.toFiniteBilinearModule = g := by
  ext x; simp

/-- Upgrading the identity bilinear morphism at odd order gives the identity quadratic morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_id (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    homOfBilinearHomOfOdd hA (FiniteBilinearModule.Hom.id A.toFiniteBilinearModule) =
      Hom.id A := by
  ext x; simp

/-- Upgrading a composite bilinear morphism at odd order gives the composite upgraded quadratic
morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_comp {C : FiniteQuadraticModule.{w}} (hA : Odd (Nat.card A))
    (hB : Odd (Nat.card B))
    (g : FiniteBilinearModule.Hom B.toFiniteBilinearModule C.toFiniteBilinearModule)
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (homOfBilinearHomOfOdd hB g).comp (homOfBilinearHomOfOdd hA f) =
      homOfBilinearHomOfOdd hA (g.comp f) := by
  ext x; simp

/-- A bilinear isometry between finite quadratic modules of odd order preserves the quadratic
maps. -/
theorem map_quadratic_of_odd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : B.quadratic (f x) = A.quadratic x := by
  have hB : Nat.card B = Nat.card A := (Nat.card_congr f.toAddEquiv.toEquiv).symm
  rw [quadratic_eq_nsmul_pairing_self_of_odd (hB ▸ hA), quadratic_eq_nsmul_pairing_self_of_odd hA,
    hB, f.map_pairing]

/-- A bilinear isometry between finite quadratic modules of odd order, as a quadratic isometry. -/
def isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Isometry A B where
  toLinearEquiv := f.toAddEquiv.toIntLinearEquiv
  map_app' := map_quadratic_of_odd hA f

/-- The quadratic isometry `isometryOfBilinearIsometryOfOdd hA f` acts as `f`. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : isometryOfBilinearIsometryOfOdd hA f x = f x :=
  (rfl)

/-- Evaluating the inverse of an odd-order upgraded bilinear isometry evaluates `f.symm`. -/
theorem isometryOfBilinearIsometryOfOdd_symm_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (y : B) : (isometryOfBilinearIsometryOfOdd hA f).symm y = f.symm y := by
  apply EquivLike.injective f
  rw [← isometryOfBilinearIsometryOfOdd_apply hA f,
    QuadraticMap.IsometryEquiv.apply_symm_apply, f.apply_symm_apply]

/-- The inverse of a bilinear isometry upgraded at odd order is the upgraded inverse bilinear
isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_symm (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).symm =
      isometryOfBilinearIsometryOfOdd (Nat.card_congr f.toAddEquiv.toEquiv ▸ hA) f.symm :=
  DFunLike.ext _ _ fun y ↦ by
    rw [isometryOfBilinearIsometryOfOdd_symm_apply, isometryOfBilinearIsometryOfOdd_apply]

/-- Upgrading a bilinear isometry at odd order preserves its underlying additive equivalence. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toAddEquiv (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toAddEquiv = f.toAddEquiv :=
  (rfl)

/-- Forgetting bijectivity of an odd-order upgraded bilinear isometry gives the upgraded bilinear
morphism. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toHom (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toHom = homOfBilinearHomOfOdd hA f.toHom := by
  ext x
  rw [Isometry.toHom_apply, isometryOfBilinearIsometryOfOdd_apply,
    homOfBilinearHomOfOdd_apply, FiniteBilinearModule.Isometry.toHom_apply]

/-- Forgetting the quadratic maps of `isometryOfBilinearIsometryOfOdd hA f` recovers `f`. -/
@[simp]
theorem toFiniteBilinearModule_isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toFiniteBilinearModule = f :=
  -- Both sides have the additive equivalence `f.toAddEquiv`, repackaged as a `ℤ`-linear one.
  FiniteBilinearModule.Isometry.toAddEquiv_injective
    (Isometry.toFiniteBilinearModule_toAddEquiv _)

/-- Upgrading the polar bilinear isometry of a quadratic isometry at odd order recovers the
quadratic isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toFiniteBilinearModule (hA : Odd (Nat.card A))
    (f : Isometry A B) :
    isometryOfBilinearIsometryOfOdd hA f.toFiniteBilinearModule = f :=
  DFunLike.ext _ _ fun x ↦
    (isometryOfBilinearIsometryOfOdd_apply hA f.toFiniteBilinearModule x).trans
      (DFunLike.congr_fun (Isometry.toFiniteBilinearModule_toAddEquiv f) x)

/-- Upgrading the identity bilinear isometry at odd order gives the identity quadratic isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_refl (A : FiniteQuadraticModule.{u})
    (hA : Odd (Nat.card A)) :
    isometryOfBilinearIsometryOfOdd hA
        (FiniteBilinearModule.Isometry.refl A.toFiniteBilinearModule) =
      QuadraticMap.IsometryEquiv.refl A.quadratic :=
  DFunLike.ext _ _ fun x ↦ by simp; rfl

/-- Upgrading a composite bilinear isometry at odd order gives the composite upgraded quadratic
isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_trans {C : FiniteQuadraticModule.{w}}
    (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (g : FiniteBilinearModule.Isometry B.toFiniteBilinearModule C.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).trans (isometryOfBilinearIsometryOfOdd hB g) =
      isometryOfBilinearIsometryOfOdd hA (f.trans g) :=
  DFunLike.ext _ _ fun x ↦ by simp

/-- Finite quadratic modules of odd order are isometric exactly when their bilinear modules are.
In odd order no Gauss-sum condition is needed, unlike Nikulin's comparison theorem
`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq`. -/
theorem nonempty_isometry_iff_bilinear_isometry_of_odd (hA : Odd (Nat.card A)) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toFiniteBilinearModule⟩, fun ⟨f⟩ ↦ ⟨isometryOfBilinearIsometryOfOdd hA f⟩⟩

end FiniteQuadraticModule

end TauCeti
