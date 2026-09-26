/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Quiver.FirstArrow
public import TauCeti.RepresentationTheory.Quiver.Representation.Comparison

/-!
# The projective resolution of a vertex simple

Let `i` be a vertex of a quiver `Q` with finitely many arrows out of it. A path out of `i` is
either trivial or an arrow `e : i ⟶ j` followed by a path out of `j`, and this decomposition is
unique. Consequently the kernel of the surjection `Pᵢ ↠ Sᵢ`, which is spanned by the paths of
positive length, is the direct sum of the projectives `Pⱼ` over the arrows `e : i ⟶ j`, embedded
by prefixing `e`. This gives the short exact sequence

```text
0 ⟶ ⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ ⟶ 0
```

of representations, a projective resolution of `Sᵢ` of length at most one. No acyclicity is
needed: cycles through `i` lie in the kernel of `Pᵢ ↠ Sᵢ` and are accounted for by the summands
`Pⱼ`. For example, for the quiver `1 ⟶ 2` it is `0 ⟶ P₂ ⟶ P₁ ⟶ S₁ ⟶ 0`, while `S₂ = P₂`
because no arrow leaves `2`.

Every invariant additive on short exact sequences therefore satisfies
`[Sᵢ] = [Pᵢ] - ∑_{e : i ⟶ j} [Pⱼ]`: this is how Euler characteristics computed on the projectives
`Pᵢ` pass to the simples.

## Main definitions

* `TauCeti.indecProjRepArrowHom`: the morphism `Pⱼ ⟶ Pᵢ` of an arrow `e : i ⟶ j`, prefixing `e`
  to a path out of `j`.
* `TauCeti.arrowSumToIndecProjRep`: the morphism `⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ` assembled from them.

## Main results

* `TauCeti.indecProjRepBasis_repr_indecProjRepArrowHom_app`: in the path bases, the morphism of
  an arrow `e` is the map `q ↦ e.toPath.comp q` on paths.
* `TauCeti.mono_arrowSumToIndecProjRep`: `⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ` is a monomorphism.
* `TauCeti.shortExact_arrowSumToIndecProjRep`: **the sequence
  `0 ⟶ ⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ ⟶ 0` is short exact.**

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), Chapter III.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

section ArrowHom

variable (k : Type u) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The morphism of an arrow**: for `e : i ⟶ j`, the morphism `Pⱼ ⟶ Pᵢ` prefixing `e` to every
path out of `j`. Under the universal property of `Pⱼ` it is the element `e` of `(Pᵢ)ⱼ`. -/
noncomputable def indecProjRepArrowHom {i j : Q} (e : i ⟶ j) :
    indecProjRep k Q j ⟶ indecProjRep k Q i :=
  indecProjRepHom j (indecProjRep k Q i) (indecProjRepBasis k i j e.toPath)

/-- The morphism of an arrow `e` sends the basis vector of a path `q` to that of `e` followed by
`q`. -/
@[simp]
theorem indecProjRepArrowHom_app_basis {i j b : Q} (e : i ⟶ j) (q : Quiver.Path j b) :
    (indecProjRepArrowHom k e).app ((Paths.of Q).obj b) (indecProjRepBasis k j b q)
      = indecProjRepBasis k i b (e.toPath.comp q) :=
  (indecProjRepHom_app_basis j (indecProjRep k Q i) _ b q).trans
    (indecProjRep_map_basis i q e.toPath)

/-- **The morphism of an arrow in the path bases**: it moves the coordinates along the injection
`q ↦ e.toPath.comp q` of paths. -/
theorem indecProjRepBasis_repr_indecProjRepArrowHom_app {i j b : Q} (e : i ⟶ j)
    (x : (indecProjRep k Q j).obj ((Paths.of Q).obj b)) :
    (indecProjRepBasis k i b).repr ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b) x)
      = Finsupp.mapDomain (fun q : Quiver.Path j b ↦ e.toPath.comp q)
          ((indecProjRepBasis k j b).repr x) := by
  have key : (indecProjRepBasis k i b).repr.toLinearMap ∘ₗ
        ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b)).hom
      = Finsupp.lmapDomain k k (fun q : Quiver.Path j b ↦ e.toPath.comp q) ∘ₗ
          (indecProjRepBasis k j b).repr.toLinearMap :=
    (indecProjRepBasis k j b).ext fun q ↦ by
      refine (congrArg (indecProjRepBasis k i b).repr (indecProjRepArrowHom_app_basis k e q)).trans
        ?_
      simp [Finsupp.mapDomain_single]
  exact LinearMap.congr_fun key x

/-- The coordinate of the image of `x` under the morphism of `e`, at `e` followed by `q`, is the
coordinate of `x` at `q`. -/
@[simp]
theorem indecProjRepBasis_repr_indecProjRepArrowHom_app_comp {i j b : Q} (e : i ⟶ j)
    (x : (indecProjRep k Q j).obj ((Paths.of Q).obj b)) (q : Quiver.Path j b) :
    (indecProjRepBasis k i b).repr ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b) x)
        (e.toPath.comp q) = (indecProjRepBasis k j b).repr x q := by
  rw [indecProjRepBasis_repr_indecProjRepArrowHom_app]
  exact Finsupp.mapDomain_apply_of_injective (Quiver.Path.comp_injective_right _) _ q

/-- The image of the morphism of an arrow `e` has no coordinate at a path starting with a
different arrow `e'`. -/
@[simp]
theorem indecProjRepBasis_repr_indecProjRepArrowHom_app_comp_of_ne {i j j' b : Q} (e : i ⟶ j)
    (e' : i ⟶ j') (h : (⟨j, e⟩ : (a : Q) × (i ⟶ a)) ≠ ⟨j', e'⟩)
    (x : (indecProjRep k Q j).obj ((Paths.of Q).obj b)) (q : Quiver.Path j' b) :
    (indecProjRepBasis k i b).repr ((indecProjRepArrowHom k e).app ((Paths.of Q).obj b) x)
        (e'.toPath.comp q) = 0 := by
  rw [indecProjRepBasis_repr_indecProjRepArrowHom_app]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨r, hr⟩
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp (Sum.inr_injective
    ((pathFirstArrowEquiv_toPath_comp e r).symm.trans
      ((congrArg (pathFirstArrowEquiv i b) hr).trans (pathFirstArrowEquiv_toPath_comp e' q))))
  exact h (congrArg _ (Prod.ext_iff.mp (eq_of_heq hh)).1)

/-- **The arrow morphisms out of a vertex are jointly injective**: at every vertex `b`, a family of
vectors whose images under the arrow morphisms sum to zero is zero. The image of the morphism of
`e` is spanned by the paths beginning with `e`, and paths beginning with different arrows are
different. -/
private theorem eq_zero_of_sum_indecProjRepArrowHom_app_eq_zero {i : Q}
    [Fintype ((j : Q) × (i ⟶ j))]
    {b : Q} (y : ∀ a : (j : Q) × (i ⟶ j), (indecProjRep k Q a.1).obj ((Paths.of Q).obj b))
    (hy : ∑ a, (indecProjRepArrowHom k a.2).app ((Paths.of Q).obj b) (y a) = 0)
    (a : (j : Q) × (i ⟶ j)) : y a = 0 := by
  obtain ⟨j, e⟩ := a
  refine (indecProjRepBasis k j b).forall_coord_eq_zero_iff.mp fun q ↦ ?_
  -- The coordinate functional of `(Pᵢ)_b`, typed on the vertex space as `hy` states it, so that
  -- `map_sum` applies to the sum in `hy`.
  let R : (indecProjRep k Q i).obj ((Paths.of Q).obj b) →ₗ[k] (Quiver.Path i b →₀ k) :=
    (indecProjRepBasis k i b).repr.toLinearMap
  have h0 := congrArg (fun x ↦ R x (e.toPath.comp q)) hy
  simp only [map_sum, Finsupp.finsetSum_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h0
  rw [Finset.sum_eq_single ⟨j, e⟩ ?_ (by simp)] at h0
  · exact (indecProjRepBasis_repr_indecProjRepArrowHom_app_comp k e _ q).symm.trans h0
  · exact fun a _ ha ↦ indecProjRepBasis_repr_indecProjRepArrowHom_app_comp_of_ne k _ _ ha _ _

variable (i : Q) [Finite ((j : Q) × (i ⟶ j))]

/-- **The kernel of `Pᵢ ↠ Sᵢ` as a direct sum**: the morphism `⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ` whose
component at `e` is the morphism `TauCeti.indecProjRepArrowHom` prefixing `e`. -/
noncomputable def arrowSumToIndecProjRep :
    (⨁ fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1) ⟶ indecProjRep k Q i :=
  biproduct.desc fun a ↦ indecProjRepArrowHom k a.2

/-- The component of `⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ` at an arrow is the morphism of that arrow. -/
@[reassoc (attr := simp)]
theorem ι_arrowSumToIndecProjRep (a : (j : Q) × (i ⟶ j)) :
    biproduct.ι (fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1) a ≫ arrowSumToIndecProjRep k i
      = indecProjRepArrowHom k a.2 :=
  biproduct.ι_desc _ a

/-- **`⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ` is a monomorphism.** -/
instance mono_arrowSumToIndecProjRep : Mono (arrowSumToIndecProjRep k i) := by
  have := Fintype.ofFinite ((j : Q) × (i ⟶ j))
  -- The decomposition `∑ₐ πₐ ≫ ιₐ = 𝟙` of the identity of the biproduct; Mathlib's
  -- `biproduct.total` only covers index types in `Type`.
  have htotal : ∑ a, biproduct.π (fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1) a ≫
      biproduct.ι (fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1) a = 𝟙 _ :=
    biproduct.hom_ext _ _ fun c ↦ by
      rw [Preadditive.sum_comp, Finset.sum_eq_single c
        (fun x _ hx ↦ by rw [Category.assoc, biproduct.ι_π_ne _ hx, comp_zero]) (by simp)]
      simp
  refine Preadditive.mono_of_cancel_zero _ fun {T} g hg ↦ biproduct.hom_ext _ _ fun a ↦ ?_
  have hsum : ∑ a, (g ≫ biproduct.π _ a) ≫ indecProjRepArrowHom k a.2 = 0 := by
    rw [← hg, ← Category.comp_id (arrowSumToIndecProjRep k i), ← Category.id_comp
      (arrowSumToIndecProjRep k i), ← htotal]
    simp [Preadditive.comp_sum, Preadditive.sum_comp]
  rw [zero_comp]
  refine NatTrans.ext (funext fun b ↦ ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_))
  rw [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  refine eq_zero_of_sum_indecProjRepArrowHom_app_eq_zero k
    (fun a ↦ (g ≫ biproduct.π _ a).app ((Paths.of Q).obj b) t) ?_ a
  have := congrArg (fun φ : T ⟶ indecProjRep k Q i ↦ φ.app ((Paths.of Q).obj b) t) hsum
  simp only [NatTrans.app_sum, ModuleCat.hom_sum, NatTrans.comp_app, ModuleCat.hom_comp,
    NatTrans.app_zero, ModuleCat.hom_zero] at this
  exact (LinearMap.sum_apply _ _ _).symm.trans this

end ArrowHom

section Resolution

variable (k : Type (max v w)) {Q : Type v} [Field k] [Quiver.{w} Q]
  (i : Q) [Finite ((j : Q) × (i ⟶ j))]

/-- The composite `⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ` vanishes: a path beginning with an arrow has
positive length. -/
@[reassoc (attr := simp)]
theorem arrowSumToIndecProjRep_comp_indecProjRepToSimpleRep :
    arrowSumToIndecProjRep k i ≫ indecProjRepToSimpleRep k i = 0 := by
  refine biproduct.hom_ext' _ _ fun a ↦ ?_
  rw [ι_arrowSumToIndecProjRep_assoc, comp_zero]
  refine (indecProjRepHomEquiv a.1 (simpleRep k Q i)).injective ?_
  rw [indecProjRepHomEquiv_comp, indecProjRepHomEquiv_apply, indecProjRepArrowHom_app_basis,
    map_zero]
  exact indecProjRepToSimpleRep_app_basis_eq_zero_of_length_ne_zero k _ (by simp)

/-- **The projective resolution of a vertex simple**: for a vertex `i` with finitely many arrows
out of it, the sequence `0 ⟶ ⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ ⟶ 0` is short exact. Both nonzero terms
before `Sᵢ` are projective, so `Sᵢ` has projective dimension at most one. -/
theorem shortExact_arrowSumToIndecProjRep :
    (ShortComplex.mk _ _ (arrowSumToIndecProjRep_comp_indecProjRepToSimpleRep k i)).ShortExact where
  exact := by
    -- Exactness is checked vertexwise: evaluation at a vertex preserves homology.
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun b ↦ ?_
    refine IsZero.of_iso ?_ (ShortComplex.mapHomologyIso _ ((evaluation _ _).obj b)).symm
    rw [← ShortComplex.exact_iff_isZero_homology, ShortComplex.moduleCat_exact_iff]
    intro x hx
    -- `change`: the evaluated short complex names its terms and maps through
    -- `ShortComplex.map`, and the vertex is an object of `Paths Q`; restating them as the vertex
    -- spaces and components at `(Paths.of Q).obj b` is what lets the basis lemmas apply.
    change Q at b
    change (indecProjRep k Q i).obj ((Paths.of Q).obj b) at x
    change (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj b) x = 0 at hx
    -- Every path in the support of `x` has positive length, so begins with an arrow `e`, and its
    -- basis vector is the image of a basis vector of the summand `Pⱼ` at `e`.
    obtain ⟨y, hy⟩ : x ∈ LinearMap.range
        ((arrowSumToIndecProjRep k i).app ((Paths.of Q).obj b)).hom := by
      refine Submodule.span_le.mpr ?_ ((indecProjRepBasis k i b).mem_span_repr_support x)
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨c, e, q, rfl, -⟩ := (Quiver.Path.length_ne_zero_iff_eq_comp p).mp fun h0 ↦ by
        obtain rfl := Quiver.Path.eq_of_length_zero p h0
        obtain rfl := Quiver.Path.eq_nil_of_length_zero p h0
        rw [indecProjRepToSimpleRep_app_self_apply] at hx
        exact Finsupp.mem_support_iff.mp hp
          ((smul_eq_zero.mp hx).resolve_right (simpleRepGenerator_ne_zero k _))
      have h := congrArg (fun φ ↦ φ.app ((Paths.of Q).obj b) (indecProjRepBasis k c b q))
        (ι_arrowSumToIndecProjRep k i ⟨c, e⟩)
      exact ⟨_, h.trans (indecProjRepArrowHom_app_basis k e q)⟩
    exact ⟨y, hy⟩

end Resolution

end TauCeti
