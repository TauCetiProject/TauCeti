/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup.Basic

/-!
# Surjective morphisms of simplicial groups are Kan fibrations

A degreewise surjective morphism of simplicial groups is a Kan fibration of the underlying
simplicial sets. The same result holds for simplicial additive groups and simplicial modules.
In particular, it applies to the quotient maps in short exact sequences of simplicial modules,
providing the lifting input for comparing their kernels with homotopy fibres.

The proof uses Moore's theorem `SSet.kanComplex_of_group`: choose a preimage of the target
simplex, fill the discrepancy on its horn in the simplicial kernel, and multiply the chosen
simplex by that correction. It does not require either a model structure on simplicial groups
or any geometric-realization comparison.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter III, Section 2.
-/

public section

universe u v

open CategoryTheory CategoryTheory.ConcreteCategory HomotopicalAlgebra Simplicial
open SSet.modelCategoryQuillen

namespace CategoryTheory.NatTrans

section Group

variable {X Y : SSet.{u}} [∀ n, Group (X.obj n)] [∀ n, Group (Y.obj n)]
  (p : X ⟶ Y)
  (hX : ∀ ⦃m n⦄ (f : m ⟶ n) (x y : X.obj m), X.map f (x * y) = X.map f x * X.map f y)
  (hp : ∀ n (x y : X.obj n), p.app n (x * y) = p.app n x * p.app n y)

include hX hp

/-- A degreewise surjective map of simplicial sets with compatible group structures is a Kan
fibration. Surjectivity is only required in positive degrees, where horn fillers live. -/
theorem fibration_of_group_of_surjective
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) : Fibration p := by
  let q (n) : X.obj n →* Y.obj n := MonoidHom.mk' (p.app n) (hp n)
  let xm {m n} (f : m ⟶ n) : X.obj m →* X.obj n := MonoidHom.mk' (X.map f) (hX f)
  -- Use the literal degreewise kernels so that a discrepancy is an element of the kernel.
  let K : SSet.{u} :=
    { obj n := (q n).ker
      map f := ↾fun x ↦ ⟨X.map f x, by
        calc
          p.app _ (X.map f x.val) = Y.map f (p.app _ x.val) :=
            congr_hom (p.naturality f) x.val
          _ = Y.map f (p.app _ 1) :=
            congrArg (Y.map f) (x.property.trans (q _).map_one.symm)
          _ = p.app _ (X.map f 1) := (congr_hom (p.naturality f) 1).symm
          _ = p.app _ 1 := congrArg (p.app _) (xm f).map_one
          _ = 1 := (q _).map_one⟩
      map_id n := by ext x; exact congr_hom (X.map_id n) x.val
      map_comp f g := by ext x; exact congr_hom (X.map_comp f g) x.val }
  let (n : SimplexCategoryᵒᵖ) : Group (K.obj n) := inferInstanceAs (Group ((q n).ker))
  have : SSet.KanComplex K := SSet.kanComplex_of_group fun _ _ f x y ↦
    Subtype.ext (hX f x.val y.val)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨x, hx⟩ := hs n (SSet.yonedaEquiv b)
  let z : Δ[n + 1] ⟶ _ := SSet.yonedaEquiv.symm x
  have hz : z ≫ p = b := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    dsimp only [z]
    rw [Equiv.apply_symm_apply]
    exact hx
  -- The discrepancy a * z⁻¹ has trivial image, by commutativity of the lifting square.
  let d : (SSet.horn (n + 1) i : SSet) ⟶ K :=
    { app m := ↾fun t ↦ ⟨a.app m t * (z.app m t.val)⁻¹, by
        have h := congr_hom (NatTrans.congr_app sq.w m) t
        have h' := congr_hom (NatTrans.congr_app hz m) t.val
        simp only [NatTrans.comp_app, types_comp_apply] at h h'
        exact (q m).mem_ker.mpr (by
          rw [map_mul, map_inv, mul_inv_eq_one]
          exact h.trans h'.symm)⟩
      naturality m l f := by
        ext t
        dsimp [K]
        rw [hX f]
        have hinv (v) := (xm f).map_inv v
        dsimp [xm, MonoidHom.mk'] at hinv
        rw [hinv]
        simp only [← NatTrans.naturality_apply]
        rfl }
  obtain ⟨c, hc⟩ := SSet.KanComplex.hornFilling d
  -- Multiplying the kernel filler on the left recovers a on the horn and still maps to b.
  let l : Δ[n + 1] ⟶ _ :=
    { app m := ↾fun t ↦ (c.app m t).val * z.app m t
      naturality m k f := by
        ext t
        dsimp
        rw [hX f, ← NatTrans.naturality_apply z f]
        exact congrArg (· * z.app k ((SSet.stdSimplex.obj _).map f t))
          (congrArg Subtype.val (NatTrans.naturality_apply c f t)) }
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · ext m t
    have h := congrArg Subtype.val (congr_hom (NatTrans.congr_app hc m) t)
    dsimp [d] at h
    dsimp [l]
    rw [← h]
    exact inv_mul_cancel_right _ _
  · ext m t
    exact (q m).map_mul _ _ |>.trans (by
      rw [(q m).mem_ker.mp (c.app m t).property, one_mul]
      exact congr_hom (NatTrans.congr_app hz m) t)

end Group

/-- A map of simplicial additive groups which is surjective in positive degrees is a Kan
fibration of the underlying simplicial sets. No commutativity assumption is needed. -/
theorem fibration_of_addGroup_of_surjective
    {X Y : SSet.{u}} [∀ n, AddGroup (X.obj n)] [∀ n, AddGroup (Y.obj n)] (p : X ⟶ Y)
    (hX : ∀ ⦃m n⦄ (f : m ⟶ n) (x y : X.obj m), X.map f (x + y) = X.map f x + X.map f y)
    (hp : ∀ n (x y : X.obj n), p.app n (x + y) = p.app n x + p.app n y)
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) : Fibration p :=
  let : ∀ n, Group (X.obj n) := fun n ↦ inferInstanceAs (Group (Multiplicative (X.obj n)))
  let : ∀ n, Group (Y.obj n) := fun n ↦ inferInstanceAs (Group (Multiplicative (Y.obj n)))
  p.fibration_of_group_of_surjective hX hp hs

/-- A morphism of simplicial groups surjective in positive degrees is a Kan fibration after
forgetting the group structure. -/
theorem fibration_whiskerRight_forget_grpCat_of_surjective
    {G H : SimplicialObject GrpCat.{u}} (p : G ⟶ H)
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) :
    Fibration (Functor.whiskerRight p (forget GrpCat)) :=
  let : ∀ n, Group ((G ⋙ forget GrpCat).obj n) := fun n ↦ inferInstanceAs (Group (G.obj n))
  let : ∀ n, Group ((H ⋙ forget GrpCat).obj n) := fun n ↦ inferInstanceAs (Group (H.obj n))
  (Functor.whiskerRight p (forget GrpCat)).fibration_of_group_of_surjective
    (fun _ _ f x y ↦ map_mul (G.map f).hom x y)
    (fun n x y ↦ map_mul (p.app n).hom x y) hs

/-- A morphism of simplicial abelian groups surjective in positive degrees is a Kan fibration
of the underlying simplicial sets. -/
theorem fibration_whiskerRight_forget_addCommGrpCat_of_surjective
    {G H : SimplicialObject AddCommGrpCat.{u}} (p : G ⟶ H)
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) :
    Fibration (Functor.whiskerRight p (forget AddCommGrpCat)) :=
  let : ∀ n, AddGroup ((G ⋙ forget AddCommGrpCat).obj n) := fun n ↦
    inferInstanceAs (AddGroup (G.obj n))
  let : ∀ n, AddGroup ((H ⋙ forget AddCommGrpCat).obj n) := fun n ↦
    inferInstanceAs (AddGroup (H.obj n))
  (Functor.whiskerRight p (forget AddCommGrpCat)).fibration_of_addGroup_of_surjective
    (fun _ _ f x y ↦ map_add (G.map f).hom x y)
    (fun n x y ↦ map_add (p.app n).hom x y) hs

/-- A morphism of simplicial modules surjective in positive degrees is a Kan fibration of the
underlying simplicial sets, over any ring. -/
theorem fibration_whiskerRight_forget_moduleCat_of_surjective
    {R : Type v} [Ring R] {G H : SimplicialObject (ModuleCat.{u} R)} (p : G ⟶ H)
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) :
    Fibration (Functor.whiskerRight p (forget (ModuleCat R))) :=
  let : ∀ n, AddGroup ((G ⋙ forget (ModuleCat R)).obj n) := fun n ↦
    inferInstanceAs (AddGroup (G.obj n))
  let : ∀ n, AddGroup ((H ⋙ forget (ModuleCat R)).obj n) := fun n ↦
    inferInstanceAs (AddGroup (H.obj n))
  (Functor.whiskerRight p (forget (ModuleCat R))).fibration_of_addGroup_of_surjective
    (fun _ _ f x y ↦ map_add (G.map f).hom x y)
    (fun n x y ↦ map_add (p.app n).hom x y) hs

/-- Epimorphisms of simplicial modules are Kan fibrations after forgetting the module
structure. In particular this applies to cokernel projections. -/
instance fibration_whiskerRight_forget_moduleCat_of_epi
    {R : Type v} [Ring R] {G H : SimplicialObject (ModuleCat.{u} R)} (p : G ⟶ H) [Epi p] :
    Fibration (Functor.whiskerRight p (forget (ModuleCat R))) :=
  p.fibration_whiskerRight_forget_moduleCat_of_surjective fun _ ↦
    (ModuleCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app p).1 inferInstance _)

end CategoryTheory.NatTrans
