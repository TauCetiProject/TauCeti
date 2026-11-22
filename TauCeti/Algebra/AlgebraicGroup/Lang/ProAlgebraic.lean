/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import TauCeti.Algebra.AlgebraicGroup.Lang.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import TauCeti.GroupTheory.FixedSubgroup.Lang

/-!
# Lang's theorem for pro-algebraic groups over finite fields

Let `F` be a finite field of cardinality `q`, let `K / F` be an algebraically closed extension,
and let `D : ι ⥤ FiniteTypeCommHopfAlgCat F` be a filtered diagram of coordinate Hopf algebras of
geometrically connected finite-type affine group schemes over `F`. Contravariantly, the groups of
`K`-points form a cofiltered inverse system of algebraic groups equipped with compatible
`q ^ n`-Frobenius endomorphisms.

For any compatible family `a_i ∈ (Spec (D i))(K)` and any positive integer `n ≠ 0`, the Lang fiber
`{g_i | g_i⁻¹ * F^n(g_i) = a_i}` at each stage `i` is:

* nonempty, by Lang's theorem for geometrically connected finite-type groups
  (`TauCeti.Lang.surjective_inv_mul_frobeniusPoints`);
* finite, because it embeds into the Frobenius-fixed subgroup of `(Spec (D i))(K)`
  (`MonoidHom.finite_setOf_inv_mul_eq` and
  `TauCeti.FiniteField.finite_fixedSubgroup_frobeniusPoints`).

Because the transition maps commute with the Frobenius, they carry Lang fibers into Lang fibers.
By the inverse-limit theorem for cofiltered systems of finite nonempty sets
(`nonempty_sections_of_finite_cofiltered_system`), the system of fibers has a compatible section:
every compatible family `a_i` admits a compatible solution `g_i` with `g_i⁻¹ * F^n(g_i) = a_i`.
Surjectivity of the transition maps on fibers is not required.

## Main results

* `TauCeti.Lang.lang_proAlgebraic_functor_surjective`: categorical form for a functor
  `D : ι ⥤ FiniteTypeCommHopfAlgCat F` indexed by a filtered (or empty) category `ι` and any
  positive iterate `n ≠ 0` of the Frobenius.
* `TauCeti.Lang.lang_proAlgebraic_surjective`: explicit transition-family form for a directed
  system `(H, f)` of geometrically connected finite-type coordinate Hopf algebras and the
  `q`-power Frobenius `σ : K →ₐ[F] K`.

## References

* J. S. Milne, *Algebraic Groups*, version 2.00 (2015), Proposition 27.54 and Corollary 27.55,
  pp. 487–488.
* T. Suzuki and M. Yoshida, *A refinement of the local class field theory of Serre and Hazewinkel*,
  RIMS Kôkyûroku Bessatsu B32 (2012), 163–191, Proposition 3.5(2), p. 176 (pro-algebraic Lang exact
  sequence in the commutative setting).
-/

public section

open CategoryTheory WithConv

universe u v w r

namespace TauCeti.Lang

variable {F : Type u} [Field F] [Fintype F]
variable {K : Type w} [Field K] [Algebra F K]

/-- The cofiltered diagram of Lang fibers `{g_i | g_i⁻¹ * F^n(g_i) = a_i}` associated to a
compatible family `a` on a diagram `D` of finite-type commutative Hopf algebras. -/
private noncomputable def langFiberFunctor
    {ι : Type r} [Category* ι]
    (D : ι ⥤ FiniteTypeCommHopfAlgCat.{u, v} F) (n : ℕ)
    (a : ∀ i, WithConv (D.obj i →ₐ[F] K))
    (ha : ∀ ⦃i j : ι⦄ (u : i ⟶ j),
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map u)) (a j) = a i) :
    ιᵒᵖ ⥤ Type (max v w) where
  obj i :=
    {g : WithConv (D.obj i.unop →ₐ[F] K) |
      g⁻¹ * FiniteField.frobeniusPoints F n g = a i.unop}
  map {i j} f := TypeCat.ofHom fun g =>
    ⟨BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map f.unop)) g.val, by
      let φ := FiniteTypeCommHopfAlgCat.toBialgHom (D.map f.unop)
      have hcomm : FiniteField.frobeniusPoints F n (BialgHom.mapDomain φ g.val) =
          BialgHom.mapDomain φ (FiniteField.frobeniusPoints F n g.val) :=
        (DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints φ n) g.val).symm
      rw [Set.mem_ofPred_eq, hcomm, ← map_inv, ← map_mul, g.property]
      exact ha f.unop⟩
  map_id i := by
    refine ConcreteCategory.hom_ext _ _ fun g => Subtype.ext ?_
    simp only [TypeCat.ofHom_apply, unop_id, D.map_id, FiniteTypeCommHopfAlgCat.toBialgHom_id,
      BialgHom.mapDomain_id, MonoidHom.id_apply, types_id_apply]
  map_comp {i j k} f₁ f₂ := by
    refine ConcreteCategory.hom_ext _ _ fun g => Subtype.ext ?_
    simp only [TypeCat.ofHom_apply, unop_comp, D.map_comp,
      FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.mapDomain_comp, MonoidHom.comp_apply,
      types_comp_apply]

/-- Underlying `K`-point of a transition map in `langFiberFunctor`. -/
private theorem langFiberFunctor_map_val
    {ι : Type r} [Category* ι]
    (D : ι ⥤ FiniteTypeCommHopfAlgCat.{u, v} F) (n : ℕ)
    (a : ∀ i, WithConv (D.obj i →ₐ[F] K))
    (ha : ∀ ⦃i j : ι⦄ (u : i ⟶ j),
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map u)) (a j) = a i)
    {i j : ιᵒᵖ} (f : i ⟶ j) (g : (langFiberFunctor D n a ha).obj i) :
    ((langFiberFunctor D n a ha).map f g).val =
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map f.unop)) g.val :=
  rfl

variable [IsAlgClosed K]

/-- **Lang's theorem for pro-algebraic groups** (categorical form): given a filtered diagram
`D : ι ⥤ FiniteTypeCommHopfAlgCat F` of geometrically connected finite-type coordinate Hopf
algebras over a finite field `F` and a positive integer `n ≠ 0`, every compatible family of
`K`-points over an algebraically closed extension `K / F` lies in the image of the coordinatewise
Lang map `g ↦ g⁻¹ * F^n(g)` on compatible families. -/
theorem lang_proAlgebraic_functor_surjective
    {ι : Type r} [Category* ι] [IsFilteredOrEmpty ι]
    (D : ι ⥤ FiniteTypeCommHopfAlgCat.{u, v} F) {n : ℕ} (hn : n ≠ 0)
    (hconn : ∀ i, geometricallyConnectedCommHopfAlgProperty F (D.obj i).obj)
    (a : ∀ i, WithConv (D.obj i →ₐ[F] K))
    (ha : ∀ ⦃i j : ι⦄ (u : i ⟶ j),
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map u)) (a j) = a i) :
    ∃ g : ∀ i, WithConv (D.obj i →ₐ[F] K),
      (∀ ⦃i j : ι⦄ (u : i ⟶ j),
        BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map u)) (g j) = g i) ∧
      ∀ i, (g i)⁻¹ * FiniteField.frobeniusPoints F n (g i) = a i := by
  let S := langFiberFunctor D n a ha
  have : ∀ i : ιᵒᵖ, Finite (S.obj i) := fun i =>
    have hfin : Finite (fixedSubgroup
        (FiniteField.frobeniusPoints F n (H := D.obj i.unop) (A := K))) :=
      FiniteField.finite_fixedSubgroup_frobeniusPoints hn
    @MonoidHom.finite_setOf_inv_mul_eq _ _
      (FiniteField.frobeniusPoints F n (H := D.obj i.unop) (A := K)) hfin (a i.unop)
  have : ∀ i : ιᵒᵖ, Nonempty (S.obj i) := fun i => by
    obtain ⟨g, hg⟩ := surjective_inv_mul_frobeniusPoints (F := F) (K := K) (H := D.obj i.unop)
      hn (hconn i.unop) (a i.unop)
    exact ⟨⟨g, hg⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system S
  refine ⟨fun i => (s (Opposite.op i)).val, ?_, fun i => (s (Opposite.op i)).property⟩
  intro i j u
  have hval := congrArg Subtype.val (hs u.op)
  rw [langFiberFunctor_map_val, Quiver.Hom.unop_op] at hval
  exact hval

/-- **Lang's theorem for pro-algebraic groups**: for a directed inverse system of geometrically
connected finite-type affine group schemes over a finite field `F` (represented contravariantly by
coordinate Hopf algebras `H i` and transition morphisms `f i j hij`) and the `|F|`-power Frobenius
`σ : K →ₐ[F] K` on an algebraically closed extension `K / F`, every compatible family `a` of
`K`-points admits a compatible solution `g` to `g_i⁻¹ * σ(g_i) = a_i`. -/
theorem lang_proAlgebraic_surjective
    {ι : Type r} [Preorder ι] [IsDirectedOrder ι]
    (H : ι → FiniteTypeCommHopfAlgCat.{u, v} F)
    (hconn : ∀ i, geometricallyConnectedCommHopfAlgProperty F (H i).obj)
    (f : ∀ i j, i ≤ j → (H i ⟶ H j))
    (fid : ∀ i, f i i le_rfl = 𝟙 (H i))
    (fcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      f i j hij ≫ f j k hjk = f i k (hij.trans hjk))
    (σ : K →ₐ[F] K)
    (hσ : ∀ z, σ z = z ^ Fintype.card F)
    (a : ∀ i, WithConv (H i →ₐ[F] K))
    (ha : ∀ i j (hij : i ≤ j),
      toConv ((a j).ofConv.comp
        (FiniteTypeCommHopfAlgCat.toBialgHom (f i j hij)).toAlgHom) = a i) :
    ∃ g : ∀ i, WithConv (H i →ₐ[F] K),
      (∀ i j (hij : i ≤ j),
        toConv ((g j).ofConv.comp
          (FiniteTypeCommHopfAlgCat.toBialgHom (f i j hij)).toAlgHom) = g i) ∧
      ∀ i, (g i)⁻¹ * toConv (σ.comp (g i).ofConv) = a i := by
  let D : ι ⥤ FiniteTypeCommHopfAlgCat.{u, v} F :=
    { obj := H
      map := fun {i j} hij => f i j (leOfHom hij)
      map_id := fun i => fid i
      map_comp := fun {i j k} hij hjk => (fcomp i j k (leOfHom hij) (leOfHom hjk)).symm }
  obtain ⟨g, hcompat, hlang⟩ := lang_proAlgebraic_functor_surjective D one_ne_zero hconn a
    (fun i j u => (BialgHom.mapDomain_apply _ _).trans (ha i j (leOfHom u)))
  refine ⟨g, fun i j hij => (BialgHom.mapDomain_apply _ _).symm.trans (hcompat (homOfLE hij)), ?_⟩
  intro i
  rw [FiniteField.toConv_comp_eq_frobeniusPoints σ (fun z => by rw [pow_one, hσ z])]
  exact hlang i

end TauCeti.Lang
