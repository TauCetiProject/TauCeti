/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis

/-!
# Group-algebra specializations of the type-A Hecke algebra

When `q = q⁻¹`, the quadratic relation is `T i * T i = 1`. For any Coxeter system `cs`
of type `A_(n-1)` on `W`, `TauCeti.TypeAHeckeAlgebra.groupAlgebraEquiv` identifies the Hecke
algebra with `MonoidAlgebra R W`, sending `T i` to the simple reflection and `T_w` to the
standard group-algebra basis vector at `w`. Its inverse sends `single w r` to `r • T_w`.
In particular, both parameters `q = 1` and `q = -1` give the ordinary group algebra with
the same generator convention, over every commutative ring, including characteristic two.

The construction uses the universal property of the Hecke presentation and the basis theorem.
No finiteness, semisimplicity, or invertibility of the order of `W` is required. The Coxeter
system parameter allows a concrete group model to be used without changing the comparison.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open CoxeterSystem

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

private noncomputable def toGroupAlgebra (hq : q = q⁻¹) :
    TypeAHeckeAlgebra R q n →ₐ[R] MonoidAlgebra R W :=
  lift (fun i ↦ MonoidAlgebra.single (cs.simple i) 1)
    (fun i ↦ by simp [← hq, MonoidAlgebra.one_def])
    (fun {i j} h ↦ by
      have hb := cs.wordProd_braidWord_eq i j
      simp only [wordProd, braidWord, coxeterMatrixA_eq_three (.inl h),
        coxeterMatrixA_eq_three (.inr h), prod_map_alternatingWord_three] at hb
      simp only [MonoidAlgebra.single_mul_single, one_mul, hb])
    (fun {i j} h ↦ by
      have hb := cs.wordProd_braidWord_eq i j
      simp only [wordProd, braidWord, coxeterMatrixA_eq_two (.inl h),
        coxeterMatrixA_eq_two (.inr h), prod_map_alternatingWord_two] at hb
      simp only [MonoidAlgebra.single_mul_single, one_mul, hb])

private theorem toGroupAlgebra_T (hq : q = q⁻¹) (i : Fin (n - 1)) :
    toGroupAlgebra cs hq (T q i) = MonoidAlgebra.single (cs.simple i) 1 :=
  lift_T _ _ _ _ i

private theorem toGroupAlgebra_Tw (hq : q = q⁻¹) (w : W) :
    toGroupAlgebra cs hq (Tw q cs w) = MonoidAlgebra.single w 1 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [Tw_wordProd cs hω, map_list_prod, List.map_map]
  simp only [Function.comp_def, toGroupAlgebra_T]
  simpa only [List.map_map, Function.comp_def, MonoidAlgebra.of_apply, wordProd] using
    ((MonoidAlgebra.of R W).map_list_prod (ω.map cs.simple)).symm

private theorem toGroupAlgebra_bijective (hq : q = q⁻¹) :
    Function.Bijective (toGroupAlgebra cs hq) := by
  let e := (basisTw q cs).equiv (MonoidAlgebra.basis W R) (Equiv.refl W)
  have he : (toGroupAlgebra cs hq).toLinearMap = e.toLinearMap := by
    apply (basisTw q cs).ext
    intro w
    calc
      _ = MonoidAlgebra.single w 1 := by simp [toGroupAlgebra_Tw]
      _ = e ((basisTw q cs) w) := by
        simpa only [MonoidAlgebra.basis_apply, Equiv.refl_apply] using
          (Module.Basis.equiv_apply (basisTw q cs) w (MonoidAlgebra.basis W R)
            (Equiv.refl W)).symm
  have hf : ⇑(toGroupAlgebra cs hq) = ⇑e := congrArg DFunLike.coe he
  rw [hf]
  exact e.bijective

/-- At any unit parameter with `q = q⁻¹`, in particular at both `1` and `-1`, the type-A
Hecke algebra is the group algebra of any Coxeter system of the corresponding type.
The generator `T i` maps to `single (cs.simple i) 1` without a sign change. -/
noncomputable def groupAlgebraEquiv (hq : q = q⁻¹) :
    TypeAHeckeAlgebra R q n ≃ₐ[R] MonoidAlgebra R W :=
  AlgEquiv.ofBijective (toGroupAlgebra cs hq) (toGroupAlgebra_bijective cs hq)

/-- The group-algebra comparison sends a Hecke generator to its simple reflection. -/
@[simp]
theorem groupAlgebraEquiv_T (hq : q = q⁻¹) (i : Fin (n - 1)) :
    groupAlgebraEquiv cs hq (T q i) = MonoidAlgebra.single (cs.simple i) 1 :=
  toGroupAlgebra_T cs hq i

/-- The group-algebra comparison sends `T_w` to the standard basis vector at `w`. -/
@[simp]
theorem groupAlgebraEquiv_Tw (hq : q = q⁻¹) (w : W) :
    groupAlgebraEquiv cs hq (Tw q cs w) = MonoidAlgebra.single w 1 :=
  toGroupAlgebra_Tw cs hq w

/-- The inverse comparison sends a group-algebra monomial to the corresponding multiple of
`T_w`. -/
@[simp]
theorem groupAlgebraEquiv_symm_single (hq : q = q⁻¹) (w : W) (r : R) :
    (groupAlgebraEquiv cs hq).symm (MonoidAlgebra.single w r) = r • Tw q cs w := by
  apply (groupAlgebraEquiv cs hq).injective
  simp

/-- The specialized Hecke representation of a braid is its image in the Coxeter group,
viewed as a group-algebra basis vector. -/
@[simp]
theorem groupAlgebraEquiv_braidHom (hq : q = q⁻¹) (b : BraidGroup n) :
    groupAlgebraEquiv cs hq (braidHom R q n b : TypeAHeckeAlgebra R q n) =
      MonoidAlgebra.single (ArtinGroup.toCoxeterGroup cs b) 1 := by
  let f := (groupAlgebraEquiv cs hq).toMonoidHom.comp
    ((Units.coeHom _).comp (braidHom R q n))
  let g := (MonoidAlgebra.of R W).comp (ArtinGroup.toCoxeterGroup cs)
  have h : f.toHomUnits = g.toHomUnits := by
    apply BraidGroup.hom_ext
    intro i
    apply Units.ext
    simp only [MonoidHom.coe_toHomUnits]
    dsimp only [f, g, MonoidHom.comp_apply]
    rw [braidHom_sigma]
    simp [BraidGroup.sigma_eq_gen]
  exact congrArg Units.val (DFunLike.congr_fun h b)

/-- The group-algebra comparisons respect the Hecke tower whenever the chosen Coxeter
systems are connected by a homomorphism preserving the indexed simple reflections. -/
theorem groupAlgebraEquiv_strandIncl (hq : q = q⁻¹) {W' : Type*} [Group W']
    (cs' : CoxeterSystem (CoxeterMatrix.A ((n + 1) - 1)) W') (f : W →* W')
    (hf : ∀ i : Fin (n - 1), f (cs.simple i) = cs'.simple (Fin.castLE (by omega) i))
    (x : TypeAHeckeAlgebra R q n) :
    groupAlgebraEquiv cs' hq (strandIncl R q n x) =
      MonoidAlgebra.mapDomainAlgHom R R f (groupAlgebraEquiv cs hq x) := by
  have h : (groupAlgebraEquiv cs' hq).toAlgHom.comp (strandIncl R q n) =
      (MonoidAlgebra.mapDomainAlgHom R R f).comp (groupAlgebraEquiv cs hq).toAlgHom := by
    apply hom_ext
    intro i
    simp [hf]
  exact DFunLike.congr_fun h x

end TauCeti.TypeAHeckeAlgebra
