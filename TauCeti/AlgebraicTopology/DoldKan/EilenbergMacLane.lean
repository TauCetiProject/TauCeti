/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.AlgebraicTopology.DoldKan.HomotopyGroups
import TauCeti.Algebra.Homology.ModuleCat.Single
import TauCeti.AlgebraicTopology.DoldKan.FunctorGamma

/-!
# The Dold–Kan model of the Eilenberg–MacLane spaces `K(A, n)`

For a module `A` over a ring `R` and `n : ℕ`, let `A[n]` be the chain complex with `A` in degree
`n` and zero elsewhere. The simplicial module `Γ(A[n])` corresponding to it under the Dold–Kan
equivalence (`TauCeti.simplicialEilenbergMacLane`) is the classical simplicial model of the
Eilenberg–MacLane space `K(A, n)`, and it is a functor of `A`; abelian groups are the case
`R = ℤ`. This file computes its combinatorial homotopy groups. Their comparison with the homotopy
groups of the geometric realization, which makes the realization a `K(A, n)` space, is not part
of this file.

Its underlying simplicial set is a Kan complex, since its simplices form groups
(`CategoryTheory.SimplicialObject.kanComplex_comp_forget_moduleCat`). The homotopy groups of the
Dold–Kan simplicial module of a chain complex are the homology groups of that complex
(`ChainComplex.doldKanPiAddEquivHomology`), and the homology of `A[n]` is `A` in degree `n` and
zero elsewhere. So at the vertex `0`:

* `π_n(K(A, n)) ≃+ A` for `n ≥ 1` (`TauCeti.simplicialEilenbergMacLanePiAddEquiv`), and
  `π₀(K(A, 0)) ≃ A` (`TauCeti.simplicialEilenbergMacLanePiZeroEquiv`), naturally in `A`
  (`TauCeti.simplicialEilenbergMacLanePiAddEquiv_map`,
  `TauCeti.simplicialEilenbergMacLanePiZeroEquiv_map`);
* every other homotopy group vanishes
  (`TauCeti.subsingleton_π_simplicialEilenbergMacLane`), and `K(A, n)` is connected for `n ≥ 1`
  (`TauCeti.subsingleton_π_zero_simplicialEilenbergMacLane`).

The identification of `π_n` with `A` is the composite of the Moore comparison
`π_n(G, 0) ≃+ H_n(N(G))` of a simplicial module `G`, the homology map of the counit
`N(Γ(A[n])) ≅ A[n]` of the Dold–Kan equivalence, and the canonical isomorphism `H_n(A[n]) ≅ A`.

The functor sends monomorphisms to monomorphisms, so an injective map `A → B` embeds `K(A, n)`
into `K(B, n)` simplexwise (`TauCeti.injective_simplicialEilenbergMacLane_map_app`); in
particular the models of submodules of `B` are simplicial submodules of the model of `B`. For a
directed family of submodules exhausting `B`, these simplicial submodules exhaust the model of
`B` (`TauCeti.exists_mem_range_simplicialEilenbergMacLane_map_app`). The simplices are the finite
sums over the summands of the splitting of `Γ(A[n])`, and on each summand the map induced by
`A → B` is the map itself (`AlgebraicTopology.DoldKan.Γ₀.map_app_on_summand`).

## References

* A. Dold, *Homology of symmetric products and other functors of complexes*, Ann. of Math. 68
  (1958), 54–80.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter III, §2.
* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967, §23.
-/

public noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe u

namespace TauCeti

variable (R : Type*) [Ring R]

/-- The Dold–Kan model of the Eilenberg–MacLane space `K(A, n)`, as a functor of the module `A`:
the simplicial module `Γ(A[n])` corresponding under the Dold–Kan equivalence to the chain complex
`A[n]` with `A` in degree `n` and zero elsewhere. -/
def simplicialEilenbergMacLane (n : ℕ) :
    ModuleCat.{u} R ⥤ SimplicialObject (ModuleCat.{u} R) :=
  single (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙ Idempotents.DoldKan.Γ

lemma simplicialEilenbergMacLane_obj (n : ℕ) (A : ModuleCat.{u} R) :
    (simplicialEilenbergMacLane R n).obj A =
      Idempotents.DoldKan.Γ.obj ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj A) :=
  (rfl)

lemma simplicialEilenbergMacLane_map (n : ℕ) {A B : ModuleCat.{u} R} (f : A ⟶ B) :
    (simplicialEilenbergMacLane R n).map f =
      eqToHom (simplicialEilenbergMacLane_obj R n A) ≫
        Idempotents.DoldKan.Γ.map ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map f) ≫
          eqToHom (simplicialEilenbergMacLane_obj R n B).symm :=
  (rfl)

variable {R}

/-- The map of homotopy groups of the Dold–Kan model of `K(-, n)` induced by a map of modules. -/
abbrev simplicialEilenbergMacLanePiMap (n k : ℕ) {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (a : SSet.KanComplex.π k ((simplicialEilenbergMacLane R n).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R n).obj A) _⦋0⦌)) :
    SSet.KanComplex.π k ((simplicialEilenbergMacLane R n).obj B ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R n).obj B) _⦋0⦌) :=
  SSet.KanComplex.π.map
    (Functor.whiskerRight ((simplicialEilenbergMacLane R n).map f) (forget (ModuleCat R)))
    (map_zero (((simplicialEilenbergMacLane R n).map f).app _).hom) a

/-- The homotopy group `π_n(K(A, n), 0)` of the Dold–Kan model is `A`, for `n ≥ 1`: the Moore
comparison `π_n(Γ(A[n]), 0) ≃+ H_n(A[n])` followed by `H_n(A[n]) ≅ A`. -/
def simplicialEilenbergMacLanePiAddEquiv (n : ℕ) (A : ModuleCat.{u} R) :
    Additive (SSet.KanComplex.π (n + 1)
      ((simplicialEilenbergMacLane R (n + 1)).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R (n + 1)).obj A) _⦋0⦌)) ≃+ A :=
  (ChainComplex.doldKanPiAddEquivHomology
    ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) (n + 1)).obj A) n).trans
    (singleObjHomologySelfIso (ComplexShape.down ℕ) (n + 1) A).toLinearEquiv.toAddEquiv

/-- The identification `π_n(K(A, n), 0) ≃+ A` is natural in the module `A`. -/
@[simp]
lemma simplicialEilenbergMacLanePiAddEquiv_map (n : ℕ) {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (a : SSet.KanComplex.π (n + 1)
      ((simplicialEilenbergMacLane R (n + 1)).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R (n + 1)).obj A) _⦋0⦌)) :
    simplicialEilenbergMacLanePiAddEquiv n B
        (.ofMul (simplicialEilenbergMacLanePiMap (n + 1) (n + 1) f a)) =
      f (simplicialEilenbergMacLanePiAddEquiv n A (.ofMul a)) :=
  (congrArg (singleObjHomologySelfIso (ComplexShape.down ℕ) (n + 1) B).hom
    (ChainComplex.doldKanPiAddEquivHomology_map
      ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) (n + 1)).map f) n a)).trans
    (ConcreteCategory.congr_hom
      (singleObjHomologySelfIso_hom_naturality (ComplexShape.down ℕ) (n + 1) f) _)

/-- The set of path components `π₀(K(A, 0), 0)` of the Dold–Kan model is `A`. -/
def simplicialEilenbergMacLanePiZeroEquiv (A : ModuleCat.{u} R) :
    SSet.KanComplex.π 0 ((simplicialEilenbergMacLane R 0).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R 0).obj A) _⦋0⦌) ≃ A :=
  (ChainComplex.doldKanPiZeroEquivHomology
    ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj A)).trans
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 A).toLinearEquiv.toEquiv

/-- The identification `π₀(K(A, 0), 0) ≃ A` is natural in the module `A`. -/
@[simp]
lemma simplicialEilenbergMacLanePiZeroEquiv_map {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (a : SSet.KanComplex.π 0 ((simplicialEilenbergMacLane R 0).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R 0).obj A) _⦋0⦌)) :
    simplicialEilenbergMacLanePiZeroEquiv B (simplicialEilenbergMacLanePiMap 0 0 f a) =
      f (simplicialEilenbergMacLanePiZeroEquiv A a) :=
  (congrArg (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 B).hom
    (ChainComplex.doldKanPiZeroEquivHomology_map
      ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map f) a)).trans
    (ConcreteCategory.congr_hom
      (singleObjHomologySelfIso_hom_naturality (ComplexShape.down ℕ) 0 f) _)

/-- The homotopy groups `π_{k+1}(K(A, n), 0)` of the Dold–Kan model vanish for `k + 1 ≠ n`. -/
theorem subsingleton_π_simplicialEilenbergMacLane {n k : ℕ} (h : k + 1 ≠ n)
    (A : ModuleCat.{u} R) :
    Subsingleton (SSet.KanComplex.π (k + 1)
      ((simplicialEilenbergMacLane R n).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R n).obj A) _⦋0⦌)) := by
  have := ModuleCat.subsingleton_of_isZero
    (isZero_single_obj_homology (ComplexShape.down ℕ) n A (k + 1) h)
  exact (ChainComplex.doldKanPiAddEquivHomology
    ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj A) k).toEquiv.subsingleton

/-- The Dold–Kan model of `K(A, n)` is connected for `n ≥ 1`: its set of path components at `0`
is a single point. -/
theorem subsingleton_π_zero_simplicialEilenbergMacLane {n : ℕ} (h : n ≠ 0)
    (A : ModuleCat.{u} R) :
    Subsingleton (SSet.KanComplex.π 0
      ((simplicialEilenbergMacLane R n).obj A ⋙ forget (ModuleCat R))
      (0 : ((simplicialEilenbergMacLane R n).obj A) _⦋0⦌)) := by
  have := ModuleCat.subsingleton_of_isZero
    (isZero_single_obj_homology (ComplexShape.down ℕ) n A 0 (Ne.symm h))
  exact (ChainComplex.doldKanPiZeroEquivHomology
    ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj A)).subsingleton

/-- The Dold–Kan model of `K(-, n)` preserves monomorphisms: `A ↦ A[n]` preserves finite limits,
and `Γ` is an equivalence. -/
instance preservesMonomorphisms_simplicialEilenbergMacLane (n : ℕ) :
    (simplicialEilenbergMacLane.{u} R n).PreservesMonomorphisms := by
  have : (Idempotents.DoldKan.Γ : ChainComplex (ModuleCat.{u} R) ℕ ⥤ _).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction
      (Abelian.DoldKan.equivalence (A := ModuleCat.{u} R)).toAdjunction
  exact Functor.preservesMonomorphisms_comp _ _

/-- An injective map of modules `A → B` induces injective maps on the simplices of the Dold–Kan
models of `K(A, n)` and `K(B, n)`: the model of a submodule is a simplicial submodule of the model
of the ambient module. -/
theorem injective_simplicialEilenbergMacLane_map_app (n : ℕ) {A B : ModuleCat.{u} R}
    (f : A ⟶ B) (hf : Function.Injective f) (m : SimplexCategoryᵒᵖ) :
    Function.Injective (((simplicialEilenbergMacLane R n).map f).app m) := by
  have : Mono f := (ModuleCat.mono_iff_injective f).2 hf
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

section DirectedUnion

variable {ι : Type*} [Nonempty ι] {B : ModuleCat.{u} R} (N : ι → Submodule R B)

/-- The Dold–Kan model of `K(B, n)` is the union of the models of the members of a directed
family of submodules exhausting `B`: every simplex comes from the model of some member. -/
theorem exists_mem_range_simplicialEilenbergMacLane_map_app (n : ℕ) (hN : Directed (· ≤ ·) N)
    (htop : ⨆ i, N i = ⊤) (Δ : SimplexCategoryᵒᵖ)
    (x : ((simplicialEilenbergMacLane R n).obj B).obj Δ) :
    ∃ i, x ∈ Set.range
      (((simplicialEilenbergMacLane R n).map (X := ModuleCat.of R (N i)) (Y := B)
        (ModuleCat.ofHom (N i).subtype)).app Δ) := by
  -- Work with `Γ₀`, the functor underlying the model, whose splitting describes the simplices.
  let K := (single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj B
  -- The images of the models of the `N i` form a directed family of submodules.
  let r (i : ι) : Submodule R (((simplicialEilenbergMacLane R n).obj B).obj Δ) :=
    LinearMap.range (((simplicialEilenbergMacLane R n).map (X := ModuleCat.of R (N i)) (Y := B)
      (ModuleCat.ofHom (N i).subtype)).app Δ).hom
  have hle {i j : ι} (h : N i ≤ N j) : r i ≤ r j := by
    rintro _ ⟨z, rfl⟩
    refine ⟨((simplicialEilenbergMacLane R n).map
      (ModuleCat.ofHom (Submodule.inclusion h))).app Δ z, ?_⟩
    rw [← Submodule.subtype_comp_inclusion (N i) (N j) h, ModuleCat.ofHom_comp, Functor.map_comp,
      NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hr : Directed (· ≤ ·) r := fun i j ↦
    let ⟨k, hik, hjk⟩ := hN i j
    ⟨k, hle hik, hle hjk⟩
  suffices h : ⨆ i, r i = ⊤ from
    (Submodule.mem_iSup_of_directed r hr).1 (h ▸ Submodule.mem_top)
  -- It suffices that the quotient by their supremum vanishes on every summand of the splitting
  -- `Γ₀.splitting` of the model, on which the map induced by `N i → B` is `(N i)[n] → B[n]`.
  rw [← Submodule.ker_mkQ (⨆ i, r i), LinearMap.ker_eq_top]
  have h0 : (ModuleCat.ofHom (⨆ i, r i).mkQ :
      ((simplicialEilenbergMacLane R n).obj B).obj Δ ⟶ ModuleCat.of R (_ ⧸ ⨆ i, r i)) = 0 := by
    refine (AlgebraicTopology.DoldKan.Γ₀.splitting K).hom_ext' _ _ fun a ↦
      ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    obtain ⟨i, y', rfl⟩ :=
      HomologicalComplex.exists_single_map_subtype_f_apply_eq (ComplexShape.down ℕ) N n hN htop _ y
    -- Both sides are applications of composites in `ModuleCat`: on the left, the class modulo
    -- `⨆ i, r i` of the image of `y` in the summand, and on the right, zero.
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_iSup_of_mem i ⟨_,
      ConcreteCategory.congr_hom (AlgebraicTopology.DoldKan.Γ₀.map_app_on_summand
        ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map (ModuleCat.ofHom (N i).subtype))
        Δ a) y'⟩)
  exact congrArg ModuleCat.Hom.hom h0

end DirectedUnion

end TauCeti
