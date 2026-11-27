/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.CategoryTheory.GradedObject.Veronese
public import TauCeti.RingTheory.GradedAlgebra.Veronese.Subalgebra

/-!
# Graded sections of the Veronese subalgebra of a graded algebra

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X`, let `d : ℕ` and let
`A^{(d)} = ⨁ₖ A_{dk}` be its `d`-th Veronese subalgebra (`CategoryTheory.CommMon.veronese`).
Over an open `U` of `X`, the graded ring of sections `⨁ₖ Γ(A_{dk}, U)` of `A^{(d)}` maps to the
graded ring of sections `⨁ₙ Γ(Aₙ, U)` of `A` by placing the degree-`k` summand in degree `d k`.
For `d ≠ 0` this identifies the graded sections of `A^{(d)}` with the Veronese subalgebra of the
graded sections of `A`, degree by degree and compatibly with restriction. This is the
affine-local input for comparing the relative `Proj` of `A^{(d)}` with that of `A`
(Stacks Project, Lemma 0B5J).

## Main declarations

* `CategoryTheory.CommMon.veroneseSectionsAlgHom`: the `Γ(X, U)`-algebra homomorphism
  `⨁ₖ Γ(A_{dk}, U) → ⨁ₙ Γ(Aₙ, U)`, sending the degree-`k` summand to degree `d k` along the
  identification `CategoryTheory.CommMon.veronese_X` of `A^{(d)}_k` with `A_{dk}`;
* `CategoryTheory.CommMon.veroneseSectionsAlgHom_restrictGradedSections`: it commutes with
  restriction of sections;
* `CategoryTheory.CommMon.veroneseSectionsEquiv`: for `d ≠ 0`, the isomorphism of
  `Γ(X, U)`-algebras from `⨁ₖ Γ(A_{dk}, U)` onto the Veronese subalgebra of `⨁ₙ Γ(Aₙ, U)`,
  carrying the degree-`k` summand onto the degree-`k` part of the Veronese grading
  (`veroneseSectionsEquiv_mem_veroneseGrading`).
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum AlgebraicGeometry

universe u

noncomputable section

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) (d : ℕ)

/-- The degree-`k` component of the `d`-th Veronese subalgebra is quasicoherent when the
degree-`d k` component of `A` is. -/
instance isQuasicoherent_veronese_X (k : ℕ) [(A.X (d * k)).IsQuasicoherent] :
    ((A.veronese d).X k).IsQuasicoherent :=
  A.veronese_X d k ▸ inferInstance

variable (U : X.Opens)

/-- Transporting a homogeneous section along an equality of degrees does not change it as an
element of the graded ring of sections. -/
private lemma of_eqToHom_app {m n : ℕ} (h : m = n) (x : Γ(A.X m, U)) :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) n ((eqToHom (congrArg A.X h)).app U x) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) m x := by
  subst h
  rfl

/-- The unit of the Veronese subalgebra, transported to degree `d · 0` of `A`, is the unit of
`A`. -/
private lemma veronese_one_comp_eqToHom :
    (A.veronese d).toMon.one ≫ eqToHom (A.veronese_X d 0) =
      A.toMon.one ≫ eqToHom (congrArg A.X (mul_zero d).symm) := by
  -- CommMon.veronese is not exposed; generalize its monoid and transport equalities
  -- so that veronese_toMon lets us use the Mon.veronese formulas.
  have key : ∀ M : Mon (GradedObject ℕ X.Modules), M = A.toMon.veronese d →
      ∀ e : M.X 0 = A.X (d * 0), M.one ≫ eqToHom e =
        A.toMon.one ≫ eqToHom (congrArg A.X (mul_zero d).symm) := by
    rintro M rfl e
    simp [Mon.veroneseOne_eq]
  exact key _ (A.veronese_toMon d) _

/-- The homogeneous multiplication of the Veronese subalgebra, transported to degree
`d (i + j)` of `A`, is the multiplication of `A` in degrees `d i` and `d j`. -/
private lemma veronese_mul_comp_eqToHom (i j : ℕ) :
    (A.veronese d).toMon.mul i j ≫ eqToHom (A.veronese_X d (i + j)) =
      (eqToHom (A.veronese_X d i) ⊗ₘ eqToHom (A.veronese_X d j)) ≫
        A.toMon.mul (d * i) (d * j) ≫ eqToHom (congrArg A.X (mul_add d i j).symm) := by
  -- CommMon.veronese is not exposed; generalize its monoid and transport equalities
  -- so that veronese_toMon lets us use the Mon.veronese formulas.
  have key : ∀ M : Mon (GradedObject ℕ X.Modules), M = A.toMon.veronese d →
      ∀ (e : ∀ k, M.X k = A.toMon.X (d * k)), M.mul i j ≫ eqToHom (e (i + j)) =
        (eqToHom (e i) ⊗ₘ eqToHom (e j)) ≫
          A.toMon.mul (d * i) (d * j) ≫ eqToHom (congrArg A.toMon.X (mul_add d i j).symm) := by
    rintro M rfl e
    simp [Mon.veroneseMul_eq]
  exact key _ (A.veronese_toMon d) (A.veronese_X d)

/-- Placing the unit of the graded sections of the Veronese subalgebra in degree `d · 0` gives the
unit of the graded sections of `A`. -/
private lemma of_veronese_gOne :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * 0) ((eqToHom (A.veronese_X d 0)).app U
        (GradedMonoid.GOne.one (A := fun k ↦ Γ((A.veronese d).X k, U)))) = 1 := by
  rw [sections_gOne_def]
  -- Fold the two applications into the application of the composite before rewriting it.
  change DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * 0)
    (((A.veronese d).toMon.one ≫ eqToHom (A.veronese_X d 0)).app U
      (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1)) = 1
  rw [veronese_one_comp_eqToHom]
  calc
    _ = DirectSum.of (fun n ↦ Γ(A.X n, U)) 0
        (A.toMon.one.app U (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) 1)) :=
      of_eqToHom_app A U (mul_zero d).symm _
    _ = DirectSum.of (fun n ↦ Γ(A.X n, U)) 0
        (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.X n, U))) := by rw [sections_gOne_def]
    _ = 1 := DirectSum.of_zero_one _

/-- Placing the product of homogeneous sections of the Veronese subalgebra in degree `d (i + j)`
gives the product of the sections placed in degrees `d i` and `d j`. -/
private lemma of_veronese_gMul {i j : ℕ} (x : Γ((A.veronese d).X i, U))
    (y : Γ((A.veronese d).X j, U)) :
    DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * (i + j)) ((eqToHom (A.veronese_X d (i + j))).app U
        (GradedMonoid.GMul.mul (A := fun k ↦ Γ((A.veronese d).X k, U)) x y)) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * i) ((eqToHom (A.veronese_X d i)).app U x) *
        DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * j) ((eqToHom (A.veronese_X d j)).app U y) := by
  rw [sections_gMul_def, DirectSum.of_mul_of, sections_gMul_def]
  -- Fold the transported product into the application of the composite before rewriting it.
  change DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * (i + j))
    ((((A.veronese d).toMon.mul i j ≫ eqToHom (A.veronese_X d (i + j))).app U)
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y))) = _
  rw [veronese_mul_comp_eqToHom]
  calc
    _ = DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * i + d * j)
        ((A.toMon.mul (d * i) (d * j)).app U
          ((eqToHom (A.veronese_X d i) ⊗ₘ eqToHom (A.veronese_X d j)).app U
            (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)))) :=
      of_eqToHom_app A U (mul_add d i j).symm _
    _ = _ := by
      apply congrArg (DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * i + d * j))
      apply congrArg ((A.toMon.mul (d * i) (d * j)).app U)
      exact (ConcreteCategory.congr_hom
        (Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor U)
          (eqToHom (A.veronese_X d i)) (eqToHom (A.veronese_X d j))) (x ⊗ₜ y)).symm

/-- The graded ring of sections of the `d`-th Veronese subalgebra maps to the graded ring of
sections of `A`, sending the degree-`k` summand `Γ(A_{dk}, U)` to degree `d k`
(`veroneseSectionsAlgHom_of`). -/
def veroneseSectionsAlgHom :
    (⨁ k, Γ((A.veronese d).X k, U)) →ₐ[Γ(X, U)] ⨁ n, Γ(A.X n, U) :=
  DirectSum.toAlgebra _ _
    (fun k ↦ (DirectSum.lof _ ℕ (fun n ↦ Γ(A.X n, U)) (d * k)).comp
      ((Scheme.Modules.sectionsFunctor U).map (eqToHom (A.veronese_X d k))).hom)
    (of_veronese_gOne A d U) (fun {_ _} x y ↦ of_veronese_gMul A d U x y)

/-- The homomorphism `veroneseSectionsAlgHom` places a homogeneous section of degree `k` of the
Veronese subalgebra in degree `d k`. -/
@[simp]
lemma veroneseSectionsAlgHom_of (k : ℕ)
    (x : Γ((A.veronese d).X k, U)) :
    A.veroneseSectionsAlgHom d U (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k x) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * k) ((eqToHom (A.veronese_X d k)).app U x) :=
  (DirectSum.toAlgebra_apply _ _ _ _ _ _).trans (DirectSum.toSemiring_of _ _ _ _ _)

/-- A homogeneous section in degree `d k` lifts along the Veronese sections map by
transporting it back to the degree-`k` component of the Veronese subalgebra. -/
private lemma veroneseSectionsAlgHom_of_inv (k : ℕ) (y : Γ(A.X (d * k), U)) :
    A.veroneseSectionsAlgHom d U
        (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k
          (((Scheme.Modules.sectionsFunctor U).mapIso (eqToIso (A.veronese_X d k))).inv y)) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) (d * k) y := by
  erw [veroneseSectionsAlgHom_of]
  exact congrArg _
    (((Scheme.Modules.sectionsFunctor U).mapIso
      (eqToIso (A.veronese_X d k))).inv_hom_id_apply y)

/-- The degree-`d k` component of the image of `x` under `veroneseSectionsAlgHom` is the
degree-`k` component of `x`. -/
@[simp]
lemma veroneseSectionsAlgHom_apply_mul (hd : d ≠ 0)
    (x : ⨁ k, Γ((A.veronese d).X k, U)) (k : ℕ) :
    A.veroneseSectionsAlgHom d U x (d * k) = (eqToHom (A.veronese_X d k)).app U (x k) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of j y =>
    rw [veroneseSectionsAlgHom_of A d U j y]
    obtain rfl | hjk := eq_or_ne j k
    · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ ((mul_right_injective₀ hd).ne hjk.symm),
        DirectSum.of_eq_of_ne _ _ _ hjk.symm, map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

/-- The image of `veroneseSectionsAlgHom` has no component in degrees not divisible by `d`. -/
lemma veroneseSectionsAlgHom_apply_of_not_dvd
    (x : ⨁ k, Γ((A.veronese d).X k, U)) {n : ℕ} (hn : ¬d ∣ n) :
    A.veroneseSectionsAlgHom d U x n = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply]
  | of j y =>
    rw [veroneseSectionsAlgHom_of A d U j y]
    exact DirectSum.of_eq_of_ne _ _ _ fun h ↦ hn (h ▸ dvd_mul_right d j)
  | add x y hx hy => rw [map_add, DirectSum.add_apply, hx, hy, add_zero]

/-- For `d ≠ 0`, `veroneseSectionsAlgHom` is injective. -/
lemma injective_veroneseSectionsAlgHom (hd : d ≠ 0) :
    Function.Injective (A.veroneseSectionsAlgHom d U) := fun x y h ↦
  DFinsupp.ext fun k ↦ by
    let e := (Scheme.Modules.sectionsFunctor U).mapIso (eqToIso (A.veronese_X d k))
    have hk := congrArg (fun z ↦ e.inv (z (d * k))) h
    simp only [veroneseSectionsAlgHom_apply_mul A d U hd] at hk
    exact (e.hom_inv_id_apply (x k)).symm.trans (hk.trans (e.hom_inv_id_apply (y k)))

/-- The image of `veroneseSectionsAlgHom` is the Veronese subalgebra of the graded ring of
sections of `A`. -/
lemma range_veroneseSectionsAlgHom :
    (A.veroneseSectionsAlgHom d U).range =
      TauCeti.GradedAlgebra.veronese (A.gradedSectionsGrading U) d := by
  apply Subalgebra.toSubmodule_injective
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of k y =>
      -- Express membership in the underlying submodule using the original algebra map.
      change A.veroneseSectionsAlgHom d U _ ∈ _
      rw [veroneseSectionsAlgHom_of]
      exact TauCeti.GradedAlgebra.mem_veronese_of_mem (A.of_mem_gradedSectionsGrading (d * k) _)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro x hx
    induction hx using Submodule.iSup_induction' with
    | mem k x hx =>
      obtain ⟨y, rfl⟩ := DirectSum.mem_summand.mp hx
      let e := (Scheme.Modules.sectionsFunctor U).mapIso (eqToIso (A.veronese_X d k))
      exact ⟨DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k (e.inv y),
        veroneseSectionsAlgHom_of_inv A d U k y⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy

/-- For `d ≠ 0`, the graded ring of sections `⨁ₖ Γ(A_{dk}, U)` of the `d`-th Veronese
subalgebra of `A` is isomorphic, as a `Γ(X, U)`-algebra, to the Veronese subalgebra of the graded
ring of sections `⨁ₙ Γ(Aₙ, U)` of `A`. -/
def veroneseSectionsEquiv (hd : d ≠ 0) :
    (⨁ k, Γ((A.veronese d).X k, U)) ≃ₐ[Γ(X, U)]
      TauCeti.GradedAlgebra.veronese (A.gradedSectionsGrading U) d :=
  (AlgEquiv.ofInjective _ (A.injective_veroneseSectionsAlgHom d U hd)).trans
    (Subalgebra.equivOfEq _ _ (A.range_veroneseSectionsAlgHom d U))

/-- The isomorphism `veroneseSectionsEquiv` is `veroneseSectionsAlgHom` with its codomain
restricted to the Veronese subalgebra. -/
@[simp]
lemma coe_veroneseSectionsEquiv (hd : d ≠ 0)
    (x : ⨁ k, Γ((A.veronese d).X k, U)) :
    (A.veroneseSectionsEquiv d U hd x : ⨁ n, Γ(A.X n, U)) = A.veroneseSectionsAlgHom d U x := by
  simp [veroneseSectionsEquiv, AlgEquiv.ofInjective_apply]

/-- The isomorphism `veroneseSectionsEquiv` carries the degree-`k` summand of the graded sections
of the Veronese subalgebra into the degree-`k` part of the Veronese grading. -/
theorem veroneseSectionsEquiv_mem_veroneseGrading (hd : d ≠ 0)
    {k : ℕ} {x : ⨁ k, Γ((A.veronese d).X k, U)}
    (hx : x ∈ (A.veronese d).gradedSectionsGrading U k) :
    A.veroneseSectionsEquiv d U hd x ∈
      TauCeti.GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d k := by
  obtain ⟨y, rfl⟩ := DirectSum.mem_summand.mp hx
  rw [TauCeti.GradedAlgebra.mem_veroneseGrading, coe_veroneseSectionsEquiv,
    veroneseSectionsAlgHom_of A d U k y]
  exact A.of_mem_gradedSectionsGrading (d * k) _

/-- The isomorphism `veroneseSectionsEquiv` carries the degree-`k` summand of the graded sections
of the Veronese subalgebra onto the degree-`k` part of the Veronese grading. -/
theorem map_veroneseSectionsEquiv_gradedSectionsGrading
    (hd : d ≠ 0) (k : ℕ) :
    ((A.veronese d).gradedSectionsGrading U k).map
        (A.veroneseSectionsEquiv d U hd).toLinearEquiv.toLinearMap =
      TauCeti.GradedAlgebra.veroneseGrading (A.gradedSectionsGrading U) d k := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact A.veroneseSectionsEquiv_mem_veroneseGrading d U hd hx
  · obtain ⟨y, hy⟩ := DirectSum.mem_summand.mp hx
    let e := (Scheme.Modules.sectionsFunctor U).mapIso (eqToIso (A.veronese_X d k))
    refine ⟨DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k (e.inv y),
      (A.veronese d).of_mem_gradedSectionsGrading k _, Subtype.ext ?_⟩
    erw [coe_veroneseSectionsEquiv A d U hd, veroneseSectionsAlgHom_of_inv]
    exact hy

variable {U} {V : X.Opens} (f : V ⟶ U)

/-- The homomorphism `veroneseSectionsAlgHom` commutes with restriction of sections. -/
theorem veroneseSectionsAlgHom_restrictGradedSections
    (x : ⨁ k, Γ((A.veronese d).X k, U)) :
    A.veroneseSectionsAlgHom d V ((A.veronese d).restrictGradedSections f x) =
      A.restrictGradedSections f (A.veroneseSectionsAlgHom d U x) := by
  refine DFunLike.congr_fun (DirectSum.ringHom_ext
    (f := (A.veroneseSectionsAlgHom d V).toRingHom.comp ((A.veronese d).restrictGradedSections f))
    (g := (A.restrictGradedSections f).comp (A.veroneseSectionsAlgHom d U).toRingHom)
    fun k y ↦ ?_) x
  calc A.veroneseSectionsAlgHom d V ((A.veronese d).restrictGradedSections f
        (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y))
      = DirectSum.of _ (d * k) ((eqToHom (A.veronese_X d k)).app V
          (((A.veronese d).X k).presheaf.map f.op y)) :=
        (congrArg _ ((A.veronese d).restrictGradedSections_of f k y)).trans
          (veroneseSectionsAlgHom_of A d V k _)
    _ = DirectSum.of _ (d * k) ((A.X (d * k)).presheaf.map f.op
          ((eqToHom (A.veronese_X d k)).app U y)) :=
        congrArg _ (PresheafOfModules.naturality_apply (eqToHom (A.veronese_X d k)).val f.op y)
    _ = A.restrictGradedSections f (A.veroneseSectionsAlgHom d U
          (DirectSum.of (fun k ↦ Γ((A.veronese d).X k, U)) k y)) :=
        ((congrArg _ (veroneseSectionsAlgHom_of A d U k y)).trans
          (A.restrictGradedSections_of f (d * k) _)).symm

end CategoryTheory.CommMon

end
