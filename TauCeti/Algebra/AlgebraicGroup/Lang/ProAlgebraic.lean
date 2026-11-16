/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Lang.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import TauCeti.GroupTheory.FixedSubgroup.Lang

/-!
# Lang's theorem for pro-algebraic groups over finite fields

Let `F` be a finite field of cardinality `q`, let `K / F` be an algebraically closed extension,
and let `D : ι ⥤ FiniteTypeCommHopfAlgCat F` be a directed system of coordinate Hopf algebras of
smooth geometrically connected finite-type affine group schemes over `F`. Contravariantly, the
groups of `K`-points form a directed inverse system of algebraic groups equipped with compatible
`q`-Frobenius endomorphisms.

For any compatible family `a_i ∈ (Spec (D i))(K)`, the Lang fiber
`{g_i | g_i⁻¹ * F(g_i) = a_i}` at each stage `i` is:

* nonempty, by Lang's theorem for smooth geometrically connected finite-type groups
  (`TauCeti.Lang.surjective_inv_mul_frobeniusPoints`);
* finite, because it embeds into the Frobenius-fixed subgroup of `(Spec (D i))(K)`
  (`MonoidHom.finite_setOf_inv_mul_eq` and
  `TauCeti.FiniteField.finite_fixedSubgroup_frobeniusPoints`).

Because the transition maps commute with the Frobenius, they carry Lang fibers into Lang fibers.
By the inverse-limit theorem for cofiltered systems of finite nonempty sets
(`nonempty_sections_of_finite_inverse_system`), the system of fibers has a compatible section:
every compatible family `a_i` admits a compatible solution `g_i` with `g_i⁻¹ * F(g_i) = a_i`.
Surjectivity of the transition maps on fibers is not required.

## Main results

* `TauCeti.Lang.lang_proAlgebraic_functor_surjective`: categorical form for a functor
  `D : ι ⥤ FiniteTypeCommHopfAlgCat F` indexed by a directed preorder `ι`.
* `TauCeti.Lang.lang_proAlgebraic_surjective`: explicit transition-family form for a directed
  system `(H, f)` of smooth geometrically connected finite-type coordinate Hopf algebras and the
  `q`-power Frobenius `σ : K →ₐ[F] K`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 27.54 and Corollary 27.55.
* T. Suzuki and T. Yoshida, *A geometric Langlands correspondence for `GL_n` over local fields*
  (pro-algebraic Lang exact sequence in the commutative setting, Proposition 3.5(2)).
-/

public section

open CategoryTheory WithConv

universe u v w r

namespace TauCeti.Lang

variable {F : Type u} [Field F] [Fintype F]
variable {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K]
variable {ι : Type r} [Preorder ι] [IsDirectedOrder ι]

/-- Each fiber of the `|F|`-Frobenius Lang map on a smooth geometrically connected finite-type group
over `F` is finite and nonempty. -/
private theorem finite_and_nonempty_langFiber (H : FiniteTypeCommHopfAlgCat.{u, v} F)
    (hsm : smoothCommHopfAlgProperty F H.obj)
    (hconn : geometricallyConnectedCommHopfAlgProperty F H.obj)
    (b : WithConv (H →ₐ[F] K)) :
    Finite {g : WithConv (H →ₐ[F] K) | g⁻¹ * FiniteField.frobeniusPoints F 1 g = b} ∧
      Nonempty {g : WithConv (H →ₐ[F] K) | g⁻¹ * FiniteField.frobeniusPoints F 1 g = b} := by
  have hfin : Finite (fixedSubgroup (FiniteField.frobeniusPoints F 1 (H := H) (A := K))) :=
    FiniteField.finite_fixedSubgroup_frobeniusPoints one_ne_zero
  have : Algebra.Smooth F H := (smoothCommHopfAlgProperty_iff H.obj).mp hsm
  obtain ⟨g, hg⟩ := surjective_inv_mul_frobeniusPoints (F := F) (K := K) (H := H) hconn b
  exact ⟨@MonoidHom.finite_setOf_inv_mul_eq _ _
    (FiniteField.frobeniusPoints F 1 (H := H) (A := K)) hfin b, ⟨⟨g, hg⟩⟩⟩

/-- **Lang's theorem for pro-algebraic groups** (categorical form): given a directed system
`D : ι ⥤ FiniteTypeCommHopfAlgCat F` of smooth geometrically connected finite-type coordinate
Hopf algebras over a finite field `F`, every compatible family of `K`-points over an algebraically
closed extension `K / F` lies in the image of the coordinatewise Lang map `g ↦ g⁻¹ * F(g)` on
compatible families. -/
theorem lang_proAlgebraic_functor_surjective
    (D : ι ⥤ FiniteTypeCommHopfAlgCat.{u, v} F)
    (hsm : ∀ i, smoothCommHopfAlgProperty F (D.obj i).obj)
    (hconn : ∀ i, geometricallyConnectedCommHopfAlgProperty F (D.obj i).obj)
    (a : ∀ i, WithConv (D.obj i →ₐ[F] K))
    (ha : ∀ ⦃i j : ι⦄ (hij : i ≤ j),
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map (homOfLE hij))) (a j) =
        a i) :
    ∃ g : ∀ i, WithConv (D.obj i →ₐ[F] K),
      (∀ ⦃i j : ι⦄ (hij : i ≤ j),
        BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map (homOfLE hij))) (g j) =
          g i) ∧
      ∀ i, (g i)⁻¹ * FiniteField.frobeniusPoints F 1 (g i) = a i := by
  let S : ιᵒᵖ ⥤ Type (max v w) :=
    { obj := fun i =>
        {g : WithConv (D.obj i.unop →ₐ[F] K) |
          g⁻¹ * FiniteField.frobeniusPoints F 1 g = a i.unop}
      map := fun {i j} f => TypeCat.ofHom fun g =>
        ⟨BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom (D.map f.unop)) g.1, by
          let φ := FiniteTypeCommHopfAlgCat.toBialgHom (D.map f.unop)
          have hcomm : FiniteField.frobeniusPoints F 1 (BialgHom.mapDomain φ g.1) =
              BialgHom.mapDomain φ (FiniteField.frobeniusPoints F 1 g.1) :=
            (DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints φ 1) g.1).symm
          rw [Set.mem_ofPred_eq, hcomm, ← map_inv, ← map_mul, g.2]
          exact ha (leOfHom f.unop)⟩
      map_id := fun i => by
        refine ConcreteCategory.hom_ext _ _ fun g => Subtype.ext ?_
        simp only [TypeCat.ofHom_apply, unop_id, D.map_id, FiniteTypeCommHopfAlgCat.toBialgHom_id,
          BialgHom.mapDomain_id, MonoidHom.id_apply, types_id_apply]
      map_comp := fun {i j k} f₁ f₂ => by
        refine ConcreteCategory.hom_ext _ _ fun g => Subtype.ext ?_
        simp only [TypeCat.ofHom_apply, unop_comp, D.map_comp,
          FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.mapDomain_comp, MonoidHom.comp_apply,
          types_comp_apply] }
  have : ∀ i : ιᵒᵖ, Finite (S.obj i) := fun i =>
    (finite_and_nonempty_langFiber (D.obj i.unop) (hsm i.unop) (hconn i.unop) (a i.unop)).1
  have : ∀ i : ιᵒᵖ, Nonempty (S.obj i) := fun i =>
    (finite_and_nonempty_langFiber (D.obj i.unop) (hsm i.unop) (hconn i.unop) (a i.unop)).2
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system S
  refine ⟨fun i => (s (Opposite.op i)).1, ?_, fun i => (s (Opposite.op i)).2⟩
  intro i j hij
  simpa only [S, TypeCat.ofHom_apply, Quiver.Hom.unop_op] using
    congrArg Subtype.val (hs (homOfLE hij).op)

/-- **Lang's theorem for pro-algebraic groups**: for a directed inverse system of smooth
geometrically connected finite-type affine group schemes over a finite field `F` (represented
contravariantly by coordinate Hopf algebras `H i` and transition morphisms `f i j hij`) and the
`|F|`-power Frobenius `σ : K →ₐ[F] K` on an algebraically closed extension `K / F`, every
compatible family `a` of `K`-points admits a compatible solution `g` to
`g_i⁻¹ * σ(g_i) = a_i`. -/
theorem lang_proAlgebraic_surjective
    (H : ι → FiniteTypeCommHopfAlgCat.{u, v} F)
    (hsm : ∀ i, smoothCommHopfAlgProperty F (H i).obj)
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
  obtain ⟨g, hcompat, hlang⟩ := lang_proAlgebraic_functor_surjective D hsm hconn a
    (fun i j hij => (BialgHom.mapDomain_apply _ _).trans (ha i j hij))
  refine ⟨g, fun i j hij => (BialgHom.mapDomain_apply _ _).symm.trans (hcompat hij), ?_⟩
  intro i
  have hF : toConv (σ.comp (g i).ofConv) = FiniteField.frobeniusPoints F 1 (g i) := by
    apply ofConv_injective
    ext h
    rw [ofConv_toConv, AlgHom.comp_apply, hσ, FiniteField.frobeniusPoints_apply_apply, pow_one,
      Nat.card_eq_fintype_card]
  rw [hF]
  exact hlang i

end TauCeti.Lang
