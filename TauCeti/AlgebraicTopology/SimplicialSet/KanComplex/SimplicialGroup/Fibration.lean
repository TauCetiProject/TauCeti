/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Evaluation
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

-- Literal degreewise kernels keep the correction internal to this proof, without a second
-- public kernel API. Naturality at one supplies the needed target map law even though no
-- compatibility of the target operators with multiplication is assumed.
private def groupKernel : SSet.{u} :=
  let q (n) : X.obj n →* Y.obj n := MonoidHom.mk' (p.app n) (hp n)
  let xm {m n} (f : m ⟶ n) : X.obj m →* X.obj n := MonoidHom.mk' (X.map f) (hX f)
  { obj n := (q n).ker
    map f := ↾fun x ↦ ⟨X.map f x, by
      have hp1 n : p.app n 1 = 1 := (q n).map_one
      have hx1 : X.map f 1 = 1 := (xm f).map_one
      have hy : Y.map f 1 = 1 := by
        simpa only [hp1, hx1] using (p.naturality_apply f 1).symm
      exact (q _).mem_ker.mpr (by
        have hx : p.app _ x.val = 1 := (q _).mem_ker.mp x.property
        exact (p.naturality_apply f x.val).trans (by simpa only [hx] using hy))⟩
    map_id n := by ext x; exact congr_hom (X.map_id n) x.val
    map_comp f g := by ext x; exact congr_hom (X.map_comp f g) x.val }

private instance groupKernelGroup (n : SimplexCategoryᵒᵖ) :
    Group ((groupKernel p hX hp).obj n) :=
  inferInstanceAs (Group (MonoidHom.mk' (p.app n) (hp n)).ker)

private instance groupKernelKanComplex : SSet.KanComplex (groupKernel p hX hp) :=
  SSet.kanComplex_of_group fun _ _ f x y ↦ Subtype.ext (hX f x.val y.val)

-- Fill the discrepancy in the kernel; this is the only use of Moore's theorem in the lift.
private lemma exists_horn_correction {n : ℕ} (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet) ⟶ X) (z : Δ[n + 1] ⟶ X)
    (h : ∀ m t, p.app m (a.app m t) = p.app m (z.app m t.val)) :
    ∃ c : Δ[n + 1] ⟶ groupKernel p hX hp,
      ∀ m t, (c.app m t.val).val = a.app m t * (z.app m t.val)⁻¹ := by
  let q (m) : X.obj m →* Y.obj m := MonoidHom.mk' (p.app m) (hp m)
  let d : (SSet.horn (n + 1) i : SSet) ⟶ groupKernel p hX hp :=
    { app m := ↾fun t ↦ ⟨a.app m t * (z.app m t.val)⁻¹, by
        exact (q m).mem_ker.mpr (by
          rw [map_mul, map_inv, mul_inv_eq_one]
          exact h m t)⟩
      naturality m l f := by
        ext t
        dsimp [groupKernel]
        apply Subtype.ext
        dsimp only [Subtype.coe_mk]
        rw [hX f]
        have hinv (v : X.obj m) : X.map f v⁻¹ = (X.map f v)⁻¹ :=
          map_inv (MonoidHom.mk' (X.map f) (hX f)) v
        rw [hinv]
        simp only [← NatTrans.naturality_apply]
        -- The horn map restricts the standard-simplex map, so their underlying simplices
        -- agree definitionally after forgetting horn membership.
        rfl }
  obtain ⟨c, hc⟩ := SSet.KanComplex.hornFilling d
  exact ⟨c, fun m t ↦ (congrArg Subtype.val (congr_hom (NatTrans.congr_app hc m) t)).symm⟩

/-- A degreewise surjective map of simplicial sets with compatible group structures is a Kan
fibration. Surjectivity is only required in positive degrees, where horn fillers live. -/
theorem fibration_of_group_of_surjective
    (hs : ∀ n : ℕ, Function.Surjective (p.app (Opposite.op ⦋n + 1⦌))) : Fibration p := by
  let q (n) : X.obj n →* Y.obj n := MonoidHom.mk' (p.app n) (hp n)
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
  obtain ⟨c, hc⟩ := exists_horn_correction p hX hp i a z (by
    intro m t
    have h := congr_hom (NatTrans.congr_app sq.w m) t
    have h' := congr_hom (NatTrans.congr_app hz m) t.val
    exact h.trans h'.symm)
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
    exact (congrArg (· * z.app m t.val) (hc m t)).trans (inv_mul_cancel_right _ _)
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
  -- Multiplicative is a type alias with the same carrier; its multiplication unfolds to
  -- addition. Thus hX and hp directly supply the multiplicative compatibility hypotheses
  -- for these transported group structures, without changing the underlying simplicial sets.
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

/-- Epimorphisms of simplicial groups are Kan fibrations after forgetting the group
structure. -/
instance fibration_whiskerRight_forget_grpCat_of_epi
    {G H : SimplicialObject GrpCat.{u}} (p : G ⟶ H) [Epi p] :
    Fibration (Functor.whiskerRight p (forget GrpCat)) :=
  p.fibration_whiskerRight_forget_grpCat_of_surjective fun _ ↦
    (GrpCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app' GrpCat p).1 inferInstance _)

/-- Epimorphisms of simplicial abelian groups are Kan fibrations after forgetting the
abelian group structure. -/
instance fibration_whiskerRight_forget_addCommGrpCat_of_epi
    {G H : SimplicialObject AddCommGrpCat.{u}} (p : G ⟶ H) [Epi p] :
    Fibration (Functor.whiskerRight p (forget AddCommGrpCat)) :=
  p.fibration_whiskerRight_forget_addCommGrpCat_of_surjective fun _ ↦
    (AddCommGrpCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app p).1 inferInstance _)

/-- Epimorphisms of simplicial modules are Kan fibrations after forgetting the module
structure. In particular this applies to cokernel projections. -/
instance fibration_whiskerRight_forget_moduleCat_of_epi
    {R : Type v} [Ring R] {G H : SimplicialObject (ModuleCat.{u} R)} (p : G ⟶ H) [Epi p] :
    Fibration (Functor.whiskerRight p (forget (ModuleCat R))) :=
  p.fibration_whiskerRight_forget_moduleCat_of_surjective fun _ ↦
    (ModuleCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app p).1 inferInstance _)

end CategoryTheory.NatTrans
