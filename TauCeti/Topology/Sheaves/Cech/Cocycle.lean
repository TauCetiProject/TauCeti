/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sheaves.Presheaf
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
public import TauCeti.Topology.Sheaves.Presheaf

/-!
# Degree one Čech cohomology of a cover as cocycles modulo coboundaries

Let `P` be a presheaf of `R`-modules on a topological space `X` and `U : ι → Opens X` a family of
opens. Mathlib's Čech complex `(cechComplexFunctor U).obj P` has as degree `n` term a categorical
product, over `a : Fin (n + 1) → ι`, of the values of `P` on categorical products of members.
This file describes its degree one cohomology in the classical form (Forster, §12):
`H¹(U, P) = Z¹(U, P) / B¹(U, P)`, where a one-cochain is a family `c i j ∈ P(U i ∩ U j)`, a
cocycle satisfies `c j k - c i k + c i j = 0` on `U i ∩ U j ∩ U k`, and a coboundary is a family
`b j - b i` with `b i ∈ P(U i)`. Repeated indices are allowed, as in the full Čech complex, and
the sign convention is the one of Mathlib's alternating coface sums (and of
`TauCeti.BergmanSpace.Cech.d₁₂`).

No finiteness of the index type and no covering hypothesis is needed. The cochains, cocycles and
their maps make sense for modules in any universe; the comparison with Mathlib's Čech complex takes
the modules in a universe `max w v` containing the index type `ι : Type w`, so that the products of
the Čech complex exist. For `ι = Fin 2` this allows modules in any universe.

## Main definitions

* `TauCeti.Topology.CechOne.d₀₁`, `TauCeti.Topology.CechOne.d₁₂`: the Čech differentials in degrees
  zero and one, on families of sections over the members and their pairwise intersections.
* `TauCeti.Topology.CechOne.cocycles₁ P U`: the submodule of one-cocycles, the kernel of `d₁₂`.
* `TauCeti.Topology.CechOne.coboundary P U`: the coboundary map from zero-cochains to cocycles.
* `TauCeti.Topology.CechOne.toHomology P U`: the class of a cocycle in the degree one cohomology
  of Mathlib's Čech complex.
* `TauCeti.Topology.CechOne.homologyLinearEquiv P U`: cocycles modulo coboundaries are isomorphic
  to that cohomology.
* `TauCeti.Topology.CechOne.cochainsMap₀ φ`, `TauCeti.Topology.CechOne.cochainsMap₁ φ` and
  `TauCeti.Topology.CechOne.cocyclesMap₁ φ`: the maps of cochains and cocycles induced by a
  refinement `φ`.
* `TauCeti.Topology.CechOne.cochainsMap₀OfHom U α`, `TauCeti.Topology.CechOne.cochainsMap₁OfHom U α`
  and `TauCeti.Topology.CechOne.cocyclesMap₁OfHom U α`: the maps induced by a morphism of
  presheaves `α`.

## Main results

* `TauCeti.Topology.CechOne.apply_self_eq_zero` and `TauCeti.Topology.CechOne.apply_swap`: a
  cocycle vanishes on the diagonal and is alternating.
* `TauCeti.Topology.CechOne.toHomology_eq_homologyπ`: the class of a cocycle `c` is the class of
  any Čech one-cycle whose coordinates are the restrictions of `c`.
* `TauCeti.Topology.CechOne.toHomology_surjective`, `TauCeti.Topology.CechOne.ker_toHomology` and
  `TauCeti.Topology.CechOne.toHomology_eq_iff`: every class is represented by a cocycle, and two
  cocycles have the same class exactly when they differ by a coboundary.
* `TauCeti.Topology.CechOne.cocyclesMap₁_id`, `TauCeti.Topology.CechOne.cocyclesMap₁_comp`,
  `TauCeti.Topology.CechOne.cocyclesMap₁OfHom_id` and
  `TauCeti.Topology.CechOne.cocyclesMap₁OfHom_comp`: the maps of cocycles are functorial; they
  send coboundaries to coboundaries (`TauCeti.Topology.CechOne.cocyclesMap₁_coboundary`) and
  commute with each other (`TauCeti.Topology.CechOne.cocyclesMap₁OfHom_comp_cocyclesMap₁`).
* `TauCeti.Topology.CechOne.toHomology_cocyclesMap₁`: compatibility with the map
  `HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechComplexMap P φ) 1` on Čech
  cohomology induced by a refinement `φ`.
* `TauCeti.Topology.CechOne.toHomology_cocyclesMap₁OfHom`: compatibility with the map induced by a
  morphism of presheaves.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_iff`: the degree one cohomology vanishes if
  and only if every cocycle is a coboundary.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_fin_two_iff`: for a family of two opens, the
  degree one cohomology vanishes if and only if every section over `U 0 ∩ U 1` is a difference of
  restrictions; this is the elementwise description of
  `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective` in
  degree one.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_of_le` and
  `TauCeti.Topology.CechOne.subsingleton_homology_one_const`: if one member contains all the
  others, or if the family is constant, the degree one cohomology vanishes.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §12.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u r v w

namespace TauCeti.Topology.CechOne

variable {X : TopCat.{u}} {R : Type r} [Ring R]

section Cochains

variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι : Type w} (U : ι → Opens X)

/-! ### Cochains, cocycles and coboundaries -/

/-- The Čech differential on zero-cochains: `(d₀₁ b) i j = b j - b i` on `U i ∩ U j`. -/
def d₀₁ : (∀ i, P.obj (op (U i))) →ₗ[R] ∀ i j, P.obj (op (U i ⊓ U j)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (P.map (homOfLE inf_le_right).op).hom ∘ₗ LinearMap.proj j -
      (P.map (homOfLE inf_le_left).op).hom ∘ₗ LinearMap.proj i

@[simp]
theorem d₀₁_apply (b : ∀ i, P.obj (op (U i))) (i j : ι) :
    d₀₁ P U b i j = P.map (homOfLE inf_le_right).op (b j) - P.map (homOfLE inf_le_left).op (b i) :=
  (rfl)

/-- The Čech differential on one-cochains: `(d₁₂ c) i j k = c j k - c i k + c i j` on
`U i ∩ U j ∩ U k`. -/
def d₁₂ : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ i j k, P.obj (op (U i ⊓ U j ⊓ U k)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op).hom ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj j) -
      (P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj i) +
      (P.map (homOfLE inf_le_left).op).hom ∘ₗ (LinearMap.proj j ∘ₗ LinearMap.proj i)

@[simp]
theorem d₁₂_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (i j k : ι) :
    d₁₂ P U c i j k =
      P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (c j k) -
        P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (c i k) +
        P.map (homOfLE inf_le_left).op (c i j) :=
  (rfl)

/-- The differential of a coboundary vanishes. -/
@[simp]
theorem d₁₂_d₀₁ (b : ∀ i, P.obj (op (U i))) : d₁₂ P U (d₀₁ P U b) = 0 := by
  funext i j k
  simp only [d₁₂_apply, d₀₁_apply, map_sub, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
    Pi.zero_apply]
  abel

/-- The one-cocycles: one-cochains whose alternating sum vanishes on every triple
intersection. -/
def cocycles₁ : Submodule R (∀ i j, P.obj (op (U i ⊓ U j))) :=
  LinearMap.ker (d₁₂ P U)

/-- The one-cocycles are the kernel of the differential `d₁₂`. -/
theorem cocycles₁_def : cocycles₁ P U = LinearMap.ker (d₁₂ P U) :=
  (rfl)

theorem mem_cocycles₁_iff {c : ∀ i j, P.obj (op (U i ⊓ U j))} :
    c ∈ cocycles₁ P U ↔ ∀ i j k,
      P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (c j k) -
        P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (c i k) +
        P.map (homOfLE inf_le_left).op (c i j) = 0 := by
  simp only [cocycles₁_def, LinearMap.mem_ker, funext_iff, d₁₂_apply, Pi.zero_apply]

/-- The differential `d₁₂` vanishes on a cocycle. -/
@[simp]
theorem d₁₂_coe (c : cocycles₁ P U) : d₁₂ P U c = 0 :=
  LinearMap.mem_ker.1 c.property

/-- A coboundary is a cocycle. -/
@[simp]
theorem d₀₁_mem_cocycles₁ (b : ∀ i, P.obj (op (U i))) : d₀₁ P U b ∈ cocycles₁ P U :=
  LinearMap.mem_ker.2 (d₁₂_d₀₁ P U b)

variable {P U} in
/-- The cocycle identity for `(i, j, k)`, restricted to any open contained in
`U i ∩ U j ∩ U k`. -/
theorem map_sub_map_add_map_eq_zero {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles₁ P U)
    {i j k : ι} {W : Opens X} (hW : W ≤ U i ⊓ U j ⊓ U k) :
    P.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))).op (c j k) -
        P.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))).op
          (c i k) +
        P.map (homOfLE (hW.trans inf_le_left)).op (c i j) = 0 := by
  have h := congrArg (P.map (homOfLE hW).op) ((mem_cocycles₁_iff P U).1 hc i j k)
  simpa only [map_add, map_sub, map_zero, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    using h

variable {P U} in
/-- A cocycle vanishes on the diagonal. -/
theorem apply_self_eq_zero {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles₁ P U) (i : ι) :
    c i i = 0 := by
  have h := map_sub_map_add_map_eq_zero hc (i := i) (j := i) (k := i) (W := U i ⊓ U i)
    (le_inf le_rfl inf_le_left)
  simpa only [TopCat.Presheaf.map_apply_eq_self, sub_self, zero_add] using h

variable {P U} in
/-- A cocycle is alternating. -/
theorem apply_swap {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles₁ P U) (i j : ι) :
    c j i = -P.map (homOfLE (le_inf inf_le_right inf_le_left)).op (c i j) := by
  have h := map_sub_map_add_map_eq_zero hc (i := i) (j := j) (k := i) (W := U j ⊓ U i)
    (le_inf (le_inf inf_le_right inf_le_left) inf_le_right)
  rw [TopCat.Presheaf.map_apply_eq_self, apply_self_eq_zero hc, map_zero, sub_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The coboundary map, from zero-cochains to one-cocycles. -/
def coboundary : (∀ i, P.obj (op (U i))) →ₗ[R] cocycles₁ P U :=
  (d₀₁ P U).codRestrict _ (d₀₁_mem_cocycles₁ P U)

@[simp]
theorem coboundary_apply_coe (b : ∀ i, P.obj (op (U i))) :
    (coboundary P U b : ∀ i j, P.obj (op (U i ⊓ U j))) = d₀₁ P U b :=
  (rfl)

/-! ### Maps of cochains

A refinement `φ` of `U` by `V` and a morphism of presheaves `α` act on cochains. These maps
commute with the differentials and with each other, and are functorial. -/

section Refinement

variable {P U} {κ : Type w} {V : κ → Opens X}
  (φ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U)

/-- Restriction of zero-cochains along a refinement `φ`: the component at `k` is the restriction of
the component at `φ.f k`. -/
def cochainsMap₀ : (∀ i, P.obj (op (U i))) →ₗ[R] ∀ k, P.obj (op (V k)) :=
  LinearMap.pi fun k ↦ (P.map (φ.φ k).op).hom ∘ₗ LinearMap.proj (φ.f k)

@[simp]
theorem cochainsMap₀_apply (b : ∀ i, P.obj (op (U i))) (k : κ) :
    cochainsMap₀ φ b k = P.map (φ.φ k).op (b (φ.f k)) :=
  (rfl)

/-- Restriction of one-cochains along a refinement `φ`: the component at `(k, l)` is the
restriction of the component at `(φ.f k, φ.f l)`. -/
def cochainsMap₁ : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ k l, P.obj (op (V k ⊓ V l)) :=
  LinearMap.pi fun k ↦ LinearMap.pi fun l ↦
    (P.map (homOfLE (inf_le_inf (leOfHom (φ.φ k)) (leOfHom (φ.φ l)))).op).hom ∘ₗ
      (LinearMap.proj (φ.f l) ∘ₗ LinearMap.proj (φ.f k))

@[simp]
theorem cochainsMap₁_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (k l : κ) :
    cochainsMap₁ φ c k l =
      P.map (homOfLE (inf_le_inf (leOfHom (φ.φ k)) (leOfHom (φ.φ l)))).op (c (φ.f k) (φ.f l)) :=
  (rfl)

/-- Restriction along a refinement commutes with the differential `d₀₁`. -/
@[simp]
theorem cochainsMap₁_d₀₁ (b : ∀ i, P.obj (op (U i))) :
    cochainsMap₁ φ (d₀₁ P U b) = d₀₁ P V (cochainsMap₀ φ b) := by
  funext k l
  simp only [cochainsMap₁_apply, d₀₁_apply, cochainsMap₀_apply, map_sub]
  congr 1 <;> exact TopCat.Presheaf.map_map_apply_eq_map_map_apply P _ _ _ _ _

theorem cochainsMap₁_mem_cocycles₁ {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles₁ P U) :
    cochainsMap₁ φ c ∈ cocycles₁ P V := by
  rw [mem_cocycles₁_iff]
  intro k l m
  have h := map_sub_map_add_map_eq_zero hc (W := V k ⊓ V l ⊓ V m)
    (inf_le_inf (inf_le_inf (leOfHom (φ.φ k)) (leOfHom (φ.φ l))) (leOfHom (φ.φ m)))
  simp only [cochainsMap₁_apply]
  convert h using 3 <;> exact TopCat.Presheaf.map_map_apply P _ _ _ _

/-- The map of cocycles induced by a refinement `φ`. -/
def cocyclesMap₁ : cocycles₁ P U →ₗ[R] cocycles₁ P V :=
  (cochainsMap₁ φ).restrict fun _ hc ↦ cochainsMap₁_mem_cocycles₁ φ hc

@[simp]
theorem cocyclesMap₁_apply_coe (c : cocycles₁ P U) :
    (cocyclesMap₁ φ c : ∀ k l, P.obj (op (V k ⊓ V l))) = cochainsMap₁ φ c :=
  (rfl)

/-- Restriction along a refinement sends a coboundary to the coboundary of the restriction. -/
@[simp]
theorem cocyclesMap₁_coboundary (b : ∀ i, P.obj (op (U i))) :
    cocyclesMap₁ φ (coboundary P U b) = coboundary P V (cochainsMap₀ φ b) :=
  Subtype.ext (cochainsMap₁_d₀₁ φ b)

/-- The identity refinement induces the identity on zero-cochains. -/
@[simp]
theorem cochainsMap₀_id : cochainsMap₀ (P := P) (𝟙 (FormalCoproduct.mk _ U)) = LinearMap.id := by
  ext b i
  simp

/-- The identity refinement induces the identity on one-cochains. -/
@[simp]
theorem cochainsMap₁_id : cochainsMap₁ (P := P) (𝟙 (FormalCoproduct.mk _ U)) = LinearMap.id := by
  ext c i j
  simp

/-- The identity refinement induces the identity on cocycles. -/
@[simp]
theorem cocyclesMap₁_id : cocyclesMap₁ (P := P) (𝟙 (FormalCoproduct.mk _ U)) = LinearMap.id := by
  ext c i j
  simp

variable {μ : Type w} {W : μ → Opens X} (ψ : FormalCoproduct.mk _ W ⟶ FormalCoproduct.mk _ V)

/-- Restriction of zero-cochains along a composite of refinements is the composite of the
restrictions. -/
@[simp]
theorem cochainsMap₀_comp : cochainsMap₀ (P := P) (ψ ≫ φ) = cochainsMap₀ ψ ∘ₗ cochainsMap₀ φ := by
  ext b m
  simp only [cochainsMap₀_apply, LinearMap.comp_apply]
  exact (TopCat.Presheaf.map_map_apply P _ _ _ _).symm

/-- Restriction of one-cochains along a composite of refinements is the composite of the
restrictions. -/
@[simp]
theorem cochainsMap₁_comp : cochainsMap₁ (P := P) (ψ ≫ φ) = cochainsMap₁ ψ ∘ₗ cochainsMap₁ φ := by
  ext c m n
  simp only [cochainsMap₁_apply, LinearMap.comp_apply]
  exact (TopCat.Presheaf.map_map_apply P _ _ _ _).symm

/-- The map of cocycles induced by a composite of refinements is the composite of the maps. -/
@[simp]
theorem cocyclesMap₁_comp : cocyclesMap₁ (P := P) (ψ ≫ φ) = cocyclesMap₁ ψ ∘ₗ cocyclesMap₁ φ := by
  ext c m n
  simp only [cocyclesMap₁_apply_coe, LinearMap.comp_apply, cochainsMap₁_comp]

end Refinement

section Presheaf

variable {P} {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R} (α : P ⟶ Q)

/-- The map of zero-cochains induced by a morphism of presheaves. -/
def cochainsMap₀OfHom : (∀ i, P.obj (op (U i))) →ₗ[R] ∀ i, Q.obj (op (U i)) :=
  LinearMap.pi fun i ↦ (α.app (op (U i))).hom ∘ₗ LinearMap.proj i

@[simp]
theorem cochainsMap₀OfHom_apply (b : ∀ i, P.obj (op (U i))) (i : ι) :
    cochainsMap₀OfHom U α b i = α.app (op (U i)) (b i) :=
  (rfl)

/-- The map of one-cochains induced by a morphism of presheaves. -/
def cochainsMap₁OfHom : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ i j, Q.obj (op (U i ⊓ U j)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (α.app (op (U i ⊓ U j))).hom ∘ₗ (LinearMap.proj j ∘ₗ LinearMap.proj i)

@[simp]
theorem cochainsMap₁OfHom_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (i j : ι) :
    cochainsMap₁OfHom U α c i j = α.app (op (U i ⊓ U j)) (c i j) :=
  (rfl)

/-- A morphism of presheaves commutes with the differential `d₀₁`. -/
@[simp]
theorem cochainsMap₁OfHom_d₀₁ (b : ∀ i, P.obj (op (U i))) :
    cochainsMap₁OfHom U α (d₀₁ P U b) = d₀₁ Q U (cochainsMap₀OfHom U α b) := by
  funext i j
  simp

theorem cochainsMap₁OfHom_mem_cocycles₁ {c : ∀ i j, P.obj (op (U i ⊓ U j))}
    (hc : c ∈ cocycles₁ P U) : cochainsMap₁OfHom U α c ∈ cocycles₁ Q U := by
  rw [mem_cocycles₁_iff]
  intro i j k
  have h := congrArg (α.app (op (U i ⊓ U j ⊓ U k))) ((mem_cocycles₁_iff P U).1 hc i j k)
  simpa only [map_add, map_sub, map_zero, NatTrans.naturality_apply, cochainsMap₁OfHom_apply]
    using h

/-- The map of cocycles induced by a morphism of presheaves. -/
def cocyclesMap₁OfHom : cocycles₁ P U →ₗ[R] cocycles₁ Q U :=
  (cochainsMap₁OfHom U α).restrict fun _ hc ↦ cochainsMap₁OfHom_mem_cocycles₁ U α hc

@[simp]
theorem cocyclesMap₁OfHom_apply_coe (c : cocycles₁ P U) :
    (cocyclesMap₁OfHom U α c : ∀ i j, Q.obj (op (U i ⊓ U j))) = cochainsMap₁OfHom U α c :=
  (rfl)

/-- A morphism of presheaves sends a coboundary to the coboundary of the image. -/
@[simp]
theorem cocyclesMap₁OfHom_coboundary (b : ∀ i, P.obj (op (U i))) :
    cocyclesMap₁OfHom U α (coboundary P U b) = coboundary Q U (cochainsMap₀OfHom U α b) :=
  Subtype.ext (cochainsMap₁OfHom_d₀₁ U α b)

/-- The identity morphism of presheaves induces the identity on zero-cochains. -/
@[simp]
theorem cochainsMap₀OfHom_id : cochainsMap₀OfHom U (𝟙 P) = LinearMap.id := by
  ext b i
  simp

/-- The identity morphism of presheaves induces the identity on one-cochains. -/
@[simp]
theorem cochainsMap₁OfHom_id : cochainsMap₁OfHom U (𝟙 P) = LinearMap.id := by
  ext c i j
  simp

/-- The identity morphism of presheaves induces the identity on cocycles. -/
@[simp]
theorem cocyclesMap₁OfHom_id : cocyclesMap₁OfHom U (𝟙 P) = LinearMap.id := by
  ext c i j
  simp

variable {S : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R} (β : Q ⟶ S)

/-- The map of zero-cochains induced by a composite of morphisms of presheaves is the composite of
the maps. -/
@[simp]
theorem cochainsMap₀OfHom_comp :
    cochainsMap₀OfHom U (α ≫ β) = cochainsMap₀OfHom U β ∘ₗ cochainsMap₀OfHom U α := by
  ext b i
  simp

/-- The map of one-cochains induced by a composite of morphisms of presheaves is the composite of
the maps. -/
@[simp]
theorem cochainsMap₁OfHom_comp :
    cochainsMap₁OfHom U (α ≫ β) = cochainsMap₁OfHom U β ∘ₗ cochainsMap₁OfHom U α := by
  ext c i j
  simp

/-- The map of cocycles induced by a composite of morphisms of presheaves is the composite of the
maps. -/
@[simp]
theorem cocyclesMap₁OfHom_comp :
    cocyclesMap₁OfHom U (α ≫ β) = cocyclesMap₁OfHom U β ∘ₗ cocyclesMap₁OfHom U α := by
  ext c i j
  simp

variable {U} {κ : Type w} {V : κ → Opens X} (φ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U)

/-- Restriction of zero-cochains along a refinement commutes with morphisms of presheaves. -/
theorem cochainsMap₀OfHom_comp_cochainsMap₀ :
    cochainsMap₀OfHom V α ∘ₗ cochainsMap₀ (P := P) φ = cochainsMap₀ φ ∘ₗ cochainsMap₀OfHom U α := by
  ext b k
  simp

/-- Restriction of one-cochains along a refinement commutes with morphisms of presheaves. -/
theorem cochainsMap₁OfHom_comp_cochainsMap₁ :
    cochainsMap₁OfHom V α ∘ₗ cochainsMap₁ (P := P) φ = cochainsMap₁ φ ∘ₗ cochainsMap₁OfHom U α := by
  ext c k l
  simp

/-- Restriction of cocycles along a refinement commutes with morphisms of presheaves. -/
theorem cocyclesMap₁OfHom_comp_cocyclesMap₁ :
    cocyclesMap₁OfHom V α ∘ₗ cocyclesMap₁ (P := P) φ = cocyclesMap₁ φ ∘ₗ cocyclesMap₁OfHom U α := by
  ext c k l
  simp

end Presheaf

end Cochains

/-! ### Comparison with Mathlib's Čech complex

From here on the modules live in a universe `max w v` containing the index type, so that the
categorical products of the Čech complex exist. The degree `n` term of
`(cechComplexFunctor U).obj P` is a categorical product of `R`-modules, whose elements are
determined by their coordinates (`coord`). Its factors are the values of `P` on categorical
products of members, which in `Opens X` are the intersections. The maps `toCochains₀`,
`toCochains₁` and `toCochains₂` read off the restrictions of the coordinates indexed by `![i]`,
`![i, j]` and `![i, j, k]`; in degrees zero and one, `ofCochains₀` and `ofCochains₁` go back. -/

section Comparison

variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w v} R) {ι : Type w} (U : ι → Opens X)

/-- Mathlib's Čech complex of `P` for `U`. -/
private abbrev K : CochainComplex (ModuleCat.{max w v} R) ℕ := (cechComplexFunctor U).obj P

/-- The coordinate of a Čech cochain indexed by `a`. -/
private def coord {n : ℕ} (a : Fin (n + 1) → ι) :
    (K P U).X n →ₗ[R] P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  (Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a).hom

/-- The Čech cochain with prescribed coordinates. -/
private def mk (n : ℕ) :
    (∀ a : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (a j)))) →ₗ[R] (K P U).X n :=
  (ModuleCat.piIsoPi fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))).inv.hom

private lemma coord_mk {n : ℕ} (f : ∀ a : Fin (n + 1) → ι, P.obj (op (∏ᶜ fun j ↦ U (a j))))
    (a : Fin (n + 1) → ι) : coord P U a (mk P U n f) = f a :=
  congr($(ModuleCat.piIsoPi_inv_kernel_ι
    (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a).hom f)

private lemma ext_coord {n : ℕ} {x y : (K P U).X n} (h : ∀ a, coord P U a x = coord P U a y) :
    x = y :=
  (Concrete.productEquiv fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))).injective
    (funext fun a ↦ (Concrete.productEquiv_apply_apply _ x a).trans
      ((h a).trans (Concrete.productEquiv_apply_apply _ y a).symm))

/-- The morphism to a categorical product of members from an open contained in each of them. -/
private def liftHom {n : ℕ} (a : Fin (n + 1) → ι) {W : Opens X} (h : ∀ j, W ≤ U (a j)) :
    W ⟶ ∏ᶜ fun j ↦ U (a j) :=
  Pi.lift fun j ↦ homOfLE (h j)

private lemma le_π {n : ℕ} (a : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (∏ᶜ fun j ↦ U (a j)) ≤ U (a j) :=
  leOfHom (Pi.π _ j)

/-- Zero-cochains of the Čech complex as families of sections over the members. -/
private def toCochains₀ : (K P U).X 0 →ₗ[R] ∀ i, P.obj (op (U i)) :=
  LinearMap.pi fun i ↦
    (P.map (liftHom U (fun _ : Fin 1 ↦ i) fun _ ↦ le_rfl).op).hom ∘ₗ coord P U _

/-- One-cochains of the Čech complex as families of sections over pairwise intersections. -/
private def toCochains₁ : (K P U).X 1 →ₗ[R] ∀ i j, P.obj (op (U i ⊓ U j)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (P.map (liftHom U ![i, j] (Fin.forall_fin_two.2 ⟨inf_le_left, inf_le_right⟩)).op).hom ∘ₗ
      coord P U _

/-- Two-cochains of the Čech complex as families of sections over triple intersections. -/
private def toCochains₂ : (K P U).X 2 →ₗ[R] ∀ i j k, P.obj (op (U i ⊓ U j ⊓ U k)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (P.map (liftHom U ![i, j, k] (Fin.forall_fin_succ.2
      ⟨inf_le_left.trans inf_le_left, Fin.forall_fin_two.2
        ⟨inf_le_left.trans inf_le_right, inf_le_right⟩⟩)).op).hom ∘ₗ coord P U _

/-- The Čech zero-cochain with the given restrictions to the members. -/
private def ofCochains₀ : (∀ i, P.obj (op (U i))) →ₗ[R] (K P U).X 0 :=
  mk P U 0 ∘ₗ LinearMap.pi fun a ↦ (P.map (homOfLE (le_π U a 0)).op).hom ∘ₗ LinearMap.proj (a 0)

/-- The Čech one-cochain with the given restrictions to the pairwise intersections. -/
private def ofCochains₁ : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] (K P U).X 1 :=
  mk P U 1 ∘ₗ LinearMap.pi fun a ↦
    (P.map (homOfLE (le_inf (le_π U a 0) (le_π U a 1))).op).hom ∘ₗ
      (LinearMap.proj (a 1) ∘ₗ LinearMap.proj (a 0))

private lemma toCochains₀_apply (x : (K P U).X 0) (i : ι) :
    toCochains₀ P U x i =
      P.map (liftHom U (fun _ : Fin 1 ↦ i) fun _ ↦ le_rfl : U i ⟶ _).op (coord P U _ x) :=
  (rfl)

private lemma toCochains₁_apply (x : (K P U).X 1) (i j : ι) :
    toCochains₁ P U x i j =
      P.map (liftHom U ![i, j] (Fin.forall_fin_two.2 ⟨inf_le_left, inf_le_right⟩) :
        U i ⊓ U j ⟶ _).op (coord P U ![i, j] x) :=
  (rfl)

private lemma toCochains₂_apply (x : (K P U).X 2) (i j k : ι) :
    toCochains₂ P U x i j k =
      P.map (liftHom U ![i, j, k] (Fin.forall_fin_succ.2
        ⟨inf_le_left.trans inf_le_left, Fin.forall_fin_two.2
          ⟨inf_le_left.trans inf_le_right, inf_le_right⟩⟩) : U i ⊓ U j ⊓ U k ⟶ _).op
        (coord P U ![i, j, k] x) :=
  (rfl)

private lemma coord_ofCochains₀ (b : ∀ i, P.obj (op (U i))) (a : Fin 1 → ι) :
    coord P U a (ofCochains₀ P U b) = P.map (homOfLE (le_π U a 0)).op (b (a 0)) :=
  coord_mk P U _ a

private lemma coord_ofCochains₁ (c : ∀ i j, P.obj (op (U i ⊓ U j))) (a : Fin 2 → ι) :
    coord P U a (ofCochains₁ P U c) =
      P.map (homOfLE (le_inf (le_π U a 0) (le_π U a 1))).op (c (a 0) (a 1)) :=
  coord_mk P U _ a

/-- A restriction of a restriction of the coordinate indexed by `b` back to the product indexed by
an equal tuple is that coordinate. -/
private lemma map_map_coord_eq_self {n : ℕ} {a b : Fin (n + 1) → ι} (h : b = a) {W : Opens X}
    (f : (∏ᶜ fun j ↦ U (a j)) ⟶ W) (g : W ⟶ ∏ᶜ fun j ↦ U (b j)) (x : (K P U).X n) :
    P.map f.op (P.map g.op (coord P U b x)) = coord P U a x := by
  subst h
  rw [TopCat.Presheaf.map_map_apply P g.op f.op (𝟙 _), TopCat.Presheaf.map_apply_eq_self]

private lemma toCochains₀_ofCochains₀ (b : ∀ i, P.obj (op (U i))) :
    toCochains₀ P U (ofCochains₀ P U b) = b := by
  funext i
  rw [toCochains₀_apply, coord_ofCochains₀, TopCat.Presheaf.map_map_apply P _ _ (𝟙 _),
    TopCat.Presheaf.map_apply_eq_self]

private lemma toCochains₁_ofCochains₁ (c : ∀ i j, P.obj (op (U i ⊓ U j))) :
    toCochains₁ P U (ofCochains₁ P U c) = c := by
  funext i j
  rw [toCochains₁_apply, coord_ofCochains₁]
  exact (TopCat.Presheaf.map_map_apply P _ _ (𝟙 _) _).trans
    (TopCat.Presheaf.map_apply_eq_self P _ _)

private lemma ofCochains₁_toCochains₁ (x : (K P U).X 1) :
    ofCochains₁ P U (toCochains₁ P U x) = x := by
  refine ext_coord P U fun a ↦ ?_
  rw [coord_ofCochains₁, toCochains₁_apply]
  exact map_map_coord_eq_self P U (funext fun j ↦ by fin_cases j <;> rfl) _ _ x

private lemma toCochains₁_injective : Function.Injective (toCochains₁ P U) :=
  Function.LeftInverse.injective (ofCochains₁_toCochains₁ P U)

private lemma toCochains₂_injective : Function.Injective (toCochains₂ P U) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine ext_coord P U fun a ↦ ?_
  have h := congrFun (congrFun (congrFun hx (a 0)) (a 1)) (a 2)
  rw [toCochains₂_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply] at h
  have h' := congrArg (P.map (homOfLE (le_inf (le_inf (le_π U a 0) (le_π U a 1))
    (le_π U a 2))).op) h
  rw [map_zero, map_map_coord_eq_self P U (funext fun j ↦ by fin_cases j <;> rfl)] at h'
  rw [h', map_zero]

/-- Restrictions of restrictions of coordinates indexed by equal tuples agree. -/
private lemma map_map_coord_eq {n : ℕ} {b b' : Fin (n + 1) → ι} (h : b = b') {W W₁ W₂ : Opens X}
    (f : W ⟶ W₁) (g : W₁ ⟶ ∏ᶜ fun j ↦ U (b j)) (f' : W ⟶ W₂) (g' : W₂ ⟶ ∏ᶜ fun j ↦ U (b' j))
    (x : (K P U).X n) :
    P.map f.op (P.map g.op (coord P U b x)) = P.map f'.op (P.map g'.op (coord P U b' x)) := by
  subst h
  exact TopCat.Presheaf.map_map_apply_eq_map_map_apply P _ _ _ _ _

/-- The coordinates of the Čech differential, as an alternating sum of restrictions. -/
private lemma coord_d {n : ℕ} (x : (K P U).X n) (k : Fin (n + 2) → ι) :
    coord P U k ((K P U).d n (n + 1) x) =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op
          (coord P U (k ∘ m.succAbove) x) := by
  have h := congr($(TauCeti.CategoryTheory.cechComplexFunctor_obj_d_comp_π U P n k).hom x)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul] at h
  exact h.trans ((LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun m _ ↦ rfl))

private lemma toCochains₁_d (y : (K P U).X 0) :
    toCochains₁ P U ((K P U).d 0 1 y) = d₀₁ P U (toCochains₀ P U y) := by
  funext i j
  rw [toCochains₁_apply, coord_d, Fin.sum_univ_two, d₀₁_apply, toCochains₀_apply,
    toCochains₀_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    ← sub_eq_add_neg, map_sub]
  congr 1 <;> refine map_map_coord_eq P U ?_ _ _ _ _ _ <;> funext t <;> fin_cases t <;> rfl

private lemma toCochains₂_d (x : (K P U).X 1) :
    toCochains₂ P U ((K P U).d 1 2 x) = d₁₂ P U (toCochains₁ P U x) := by
  funext i j k
  rw [toCochains₂_apply, coord_d, Fin.sum_univ_three, d₁₂_apply, toCochains₁_apply,
    toCochains₁_apply, toCochains₁_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two,
    map_add, ← sub_eq_add_neg, map_sub, neg_one_sq]
  congr 1
  · congr 1 <;> refine map_map_coord_eq P U ?_ _ _ _ _ _ <;> funext t <;> fin_cases t <;> rfl
  · refine map_map_coord_eq P U ?_ _ _ _ _ _
    funext t
    fin_cases t <;> rfl

private lemma d_ofCochains₁ {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles₁ P U) :
    (K P U).d 1 2 (ofCochains₁ P U c) = 0 :=
  toCochains₂_injective P U (by
    rw [toCochains₂_d, toCochains₁_ofCochains₁, map_zero]
    exact LinearMap.mem_ker.1 hc)

private lemma toCochains₁_mem {w : (K P U).X 1} (hw : (K P U).d 1 2 w = 0) :
    toCochains₁ P U w ∈ cocycles₁ P U := by
  rw [cocycles₁_def, LinearMap.mem_ker, ← toCochains₂_d, hw, map_zero]

private lemma d_ofCochains₀ (b : ∀ i, P.obj (op (U i))) :
    (K P U).d 0 1 (ofCochains₀ P U b) = ofCochains₁ P U (d₀₁ P U b) :=
  toCochains₁_injective P U (by
    rw [toCochains₁_d, toCochains₀_ofCochains₀, toCochains₁_ofCochains₁])

/-! ### Cocycles compute degree one Čech cohomology -/

/-- The class in degree one Čech cohomology of a one-cocycle. -/
def toHomology : cocycles₁ P U →ₗ[R] ((cechComplexFunctor U).obj P).homology 1 :=
  (K P U).moduleCatHomologyClass (CochainComplex.next ℕ 1)
    (ofCochains₁ P U ∘ₗ (cocycles₁ P U).subtype) fun c ↦ d_ofCochains₁ P U c.property

/-- **The class of a cocycle as a Čech homology class.** The class of a cocycle `c` is the class of
any Čech one-cycle `z` whose coordinate indexed by `a : Fin 2 → ι` is the restriction of
`c (a 0) (a 1)` to the product of `U (a 0)` and `U (a 1)`. -/
theorem toHomology_eq_homologyπ (c : cocycles₁ P U) (z : ((cechComplexFunctor U).obj P).cycles 1)
    (hz : ∀ a : Fin 2 → ι,
      Pi.π (fun a : Fin 2 → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a
          (((cechComplexFunctor U).obj P).iCycles 1 z) =
        P.map (homOfLE (le_inf (leOfHom (Pi.π _ 0)) (leOfHom (Pi.π _ 1)))).op
          ((c : ∀ i j, P.obj (op (U i ⊓ U j))) (a 0) (a 1))) :
    toHomology P U c = ((cechComplexFunctor U).obj P).homologyπ 1 z := by
  rw [toHomology, HomologicalComplex.moduleCatHomologyClass_apply]
  congr 1
  refine (K P U).moduleCat_iCycles_injective 1 ?_
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk]
  exact ext_coord P U fun a ↦ (coord_ofCochains₁ P U c a).trans (hz a).symm

/-- Every degree one Čech cohomology class is the class of a cocycle. -/
theorem toHomology_surjective : Function.Surjective (toHomology P U) :=
  (K P U).moduleCatHomologyClass_surjective _ _ _ fun x hx ↦
    ⟨⟨_, toCochains₁_mem P U hx⟩, ofCochains₁_toCochains₁ P U x⟩

/-- A cocycle has zero class in degree one Čech cohomology if and only if it is the differential of
a zero-cochain. -/
theorem toHomology_eq_zero_iff (c : cocycles₁ P U) :
    toHomology P U c = 0 ↔ ∃ b, d₀₁ P U b = c := by
  rw [toHomology, HomologicalComplex.moduleCatHomologyClass_eq_zero_iff
    (hp := CochainComplex.prev_nat_succ 0)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨toCochains₀ P U y, ?_⟩
    rw [← toCochains₁_d, hy, LinearMap.comp_apply, Submodule.subtype_apply,
      toCochains₁_ofCochains₁]
  · rintro ⟨b, hb⟩
    exact ⟨ofCochains₀ P U b, by rw [d_ofCochains₀, hb]; rfl⟩

/-- A cocycle has zero class in degree one Čech cohomology if and only if it is a
coboundary. -/
theorem ker_toHomology : LinearMap.ker (toHomology P U) = LinearMap.range (coboundary P U) := by
  ext c
  rw [LinearMap.mem_ker, toHomology_eq_zero_iff, LinearMap.mem_range]
  exact exists_congr fun b ↦ by rw [Subtype.ext_iff, coboundary_apply_coe]

/-- Two cocycles have the same class if and only if they differ by the differential of a
zero-cochain. -/
theorem toHomology_eq_iff (c c' : cocycles₁ P U) :
    toHomology P U c = toHomology P U c' ↔
      ∃ b, d₀₁ P U b = (c : ∀ i j, P.obj (op (U i ⊓ U j))) - c' := by
  rw [← sub_eq_zero, ← map_sub, toHomology_eq_zero_iff, Submodule.coe_sub]

/-- A coboundary has zero class in degree one Čech cohomology. -/
@[simp]
theorem toHomology_coboundary (b : ∀ i, P.obj (op (U i))) :
    toHomology P U (coboundary P U b) = 0 :=
  (toHomology_eq_zero_iff P U _).2 ⟨b, rfl⟩

/-- **Degree one Čech cohomology as cocycles modulo coboundaries.** -/
def homologyLinearEquiv :
    (cocycles₁ P U ⧸ LinearMap.range (coboundary P U)) ≃ₗ[R]
      ((cechComplexFunctor U).obj P).homology 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_toHomology P U).symm).trans
    ((toHomology P U).quotKerEquivOfSurjective (toHomology_surjective P U))

@[simp]
theorem homologyLinearEquiv_mk (c : cocycles₁ P U) :
    homologyLinearEquiv P U (Submodule.Quotient.mk c) = toHomology P U c := by
  simp [homologyLinearEquiv]

@[simp]
theorem homologyLinearEquiv_symm_toHomology (c : cocycles₁ P U) :
    (homologyLinearEquiv P U).symm (toHomology P U c) = Submodule.Quotient.mk c := by
  rw [LinearEquiv.symm_apply_eq, homologyLinearEquiv_mk]

/-! ### Naturality -/

section ChainMap

variable {P U} {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w v} R} {κ : Type w} {V : κ → Opens X}

/-- The class of the image of a cocycle under a map `g` of cocycles is the image of its class under
a chain map `f` of Čech complexes that acts on one-cochains through `g`. -/
private lemma homologyMap_toHomology (f : K P U ⟶ K Q V)
    (g : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ k l, Q.obj (op (V k ⊓ V l)))
    (hg : ∀ x, toCochains₁ Q V (f.f 1 x) = g (toCochains₁ P U x))
    (g' : cocycles₁ P U →ₗ[R] cocycles₁ Q V) (hg' : ∀ c, (g' c : ∀ k l, _) = g c)
    (c : cocycles₁ P U) :
    HomologicalComplex.homologyMap f 1 (toHomology P U c) = toHomology Q V (g' c) :=
  HomologicalComplex.homologyMap_moduleCatHomologyClass _ _ _ f _ _ g'
    (fun c ↦ toCochains₁_injective Q V <| (hg _).trans <| by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.subtype_apply, toCochains₁_ofCochains₁, toCochains₁_ofCochains₁, hg'])
    c

end ChainMap

section Refinement

variable {P U} {κ : Type w} {V : κ → Opens X}
  (φ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U)

private lemma toCochains₁_cechComplexMap (x : (K P U).X 1) :
    toCochains₁ P V ((TauCeti.CategoryTheory.cechComplexMap P φ).f 1 x) =
      cochainsMap₁ φ (toCochains₁ P U x) := by
  funext k l
  have h := congr($(TauCeti.CategoryTheory.cechComplexMap_f_π P φ 1 ![k, l]).hom x)
  rw [toCochains₁_apply, cochainsMap₁_apply, toCochains₁_apply]
  -- `h` computes the coordinate of the image, which is what `coord` unfolds to.
  refine (congrArg _ h).trans ?_
  refine map_map_coord_eq P U ?_ _ _ _ _ x
  funext t
  fin_cases t <;> rfl

/-- The class of the restriction of a cocycle along a refinement `φ` is the image of its class
under the map on Čech cohomology induced by `φ`. -/
@[simp]
theorem toHomology_cocyclesMap₁ (c : cocycles₁ P U) :
    toHomology P V (cocyclesMap₁ φ c) =
      HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechComplexMap P φ) 1
        (toHomology P U c) :=
  (homologyMap_toHomology _ _ (toCochains₁_cechComplexMap φ) _ (fun _ ↦ rfl) c).symm

end Refinement

section Presheaf

variable {P} {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{max w v} R} (α : P ⟶ Q)

private lemma toCochains₁_cechComplexFunctor_map (x : (K P U).X 1) :
    toCochains₁ Q U (((cechComplexFunctor U).map α).f 1 x) =
      cochainsMap₁OfHom U α (toCochains₁ P U x) := by
  funext i j
  have h := congr($(TauCeti.CategoryTheory.cechComplexFunctor_map_f_π U P α 1 ![i, j]).hom x)
  rw [toCochains₁_apply, cochainsMap₁OfHom_apply, toCochains₁_apply]
  -- `h` computes the coordinate of the image, which is what `coord` unfolds to.
  exact (congrArg _ h).trans (NatTrans.naturality_apply α _ _).symm

/-- The class of the image of a cocycle under a morphism of presheaves `α` is the image of its
class under the map on Čech cohomology induced by `α`. -/
@[simp]
theorem toHomology_cocyclesMap₁OfHom (c : cocycles₁ P U) :
    toHomology Q U (cocyclesMap₁OfHom U α c) =
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) 1 (toHomology P U c) :=
  (homologyMap_toHomology _ _ (toCochains₁_cechComplexFunctor_map U α) _ (fun _ ↦ rfl) c).symm

end Presheaf

/-! ### Checks -/

/-- The degree one Čech cohomology vanishes if and only if every cocycle is a coboundary. -/
theorem subsingleton_homology_one_iff :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) ↔
      ∀ c ∈ cocycles₁ P U, ∃ b, d₀₁ P U b = c := by
  rw [← (homologyLinearEquiv P U).toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top]
  refine ⟨fun h c hc ↦ ?_, fun h c ↦ ?_⟩
  · obtain ⟨b, hb⟩ := h ⟨c, hc⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · obtain ⟨b, hb⟩ := h c c.property
    exact ⟨b, Subtype.ext hb⟩

/-- If one member of the family contains all the others, the degree one Čech cohomology
vanishes. -/
theorem subsingleton_homology_one_of_le (i₀ : ι) (h : ∀ i, U i ≤ U i₀) :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) := by
  -- A cocycle `c` is the coboundary of the restrictions of `c i₀ i` to `U i`.
  refine (subsingleton_homology_one_iff P U).2 fun c hc ↦
    ⟨fun i ↦ P.map (homOfLE (le_inf (h i) le_rfl)).op (c i₀ i), funext fun i ↦ funext fun j ↦ ?_⟩
  have hc' := map_sub_map_add_map_eq_zero hc (i := i₀) (j := i) (k := j) (W := U i ⊓ U j)
    (le_inf (le_inf (inf_le_left.trans (h i)) inf_le_left) inf_le_right)
  rw [TopCat.Presheaf.map_apply_eq_self] at hc'
  rw [d₀₁_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    homOfLE_comp, homOfLE_comp]
  rw [← sub_eq_zero, ← neg_eq_zero, ← hc']
  abel

/-- **Check.** A constant family has vanishing degree one Čech cohomology. -/
theorem subsingleton_homology_one_const (W : Opens X) :
    Subsingleton (((cechComplexFunctor fun _ : ι ↦ W).obj P).homology 1) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    exact (subsingleton_homology_one_iff P _).2 fun _ _ ↦
      ⟨fun i ↦ isEmptyElim i, funext fun i ↦ isEmptyElim i⟩
  | inr _ => exact subsingleton_homology_one_of_le P _ (Classical.arbitrary ι) fun _ ↦ le_rfl

end Comparison

/-- **Check.** For a family of two opens `U 0` and `U 1`, the degree one Čech cohomology vanishes
if and only if every section over `U 0 ∩ U 1` is the difference of the restrictions of a section
over `U 0` and a section over `U 1`. This is the degree one part of
`TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective`. -/
theorem subsingleton_homology_one_fin_two_iff (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R)
    (U : Fin 2 → Opens X) :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) ↔
      Function.Surjective fun x : P.obj (op (U 0)) × P.obj (op (U 1)) ↦
        P.map (homOfLE inf_le_left : U 0 ⊓ U 1 ⟶ U 0).op x.1 -
          P.map (homOfLE inf_le_right : U 0 ⊓ U 1 ⟶ U 1).op x.2 := by
  rw [subsingleton_homology_one_iff.{u, r, v, 0}]
  constructor
  · -- A section `s` over `U 0 ∩ U 1` extends to an alternating cocycle `c` with `c 0 1 = s`;
    -- minus a zero-cochain with coboundary `c` gives a preimage of `s`.
    intro h s
    let c : ∀ i j, P.obj (op (U i ⊓ U j)) := fun
      | 0, 0 => 0
      | 0, 1 => s
      | 1, 0 => -P.map (homOfLE (le_inf inf_le_right inf_le_left)).op s
      | 1, 1 => 0
    have hc : c ∈ cocycles₁ P U := by
      rw [mem_cocycles₁_iff]
      intro i j k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [c, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    obtain ⟨b, hb⟩ := h c hc
    refine ⟨(-b 0, -b 1), ?_⟩
    have h01 : P.map (homOfLE inf_le_right).op (b 1) - P.map (homOfLE inf_le_left).op (b 0) = s :=
      (d₀₁_apply P U b 0 1).symm.trans (congrFun (congrFun hb 0) 1)
    simp only [map_neg, ← h01]
    abel
  · -- A cocycle `c` is determined by `c 0 1`, so it is the coboundary of minus a preimage of
    -- `c 0 1`; the diagonal and the swapped entries follow from the cocycle identities.
    intro h c hc
    obtain ⟨x, hx⟩ := h (c 0 1)
    let b : ∀ i, P.obj (op (U i)) := fun
      | 0 => -x.1
      | 1 => -x.2
    refine ⟨b, funext fun i ↦ funext fun j ↦ ?_⟩
    match i, j with
    | 0, 0 => simp [b, apply_self_eq_zero hc]
    | 0, 1 =>
      simp only [d₀₁_apply, b, map_neg, ← hx]
      abel
    | 1, 0 =>
      rw [apply_swap hc, ← hx]
      simp only [d₀₁_apply, b, map_neg, map_sub, ← Functor.map_comp_apply, ← op_comp,
        homOfLE_comp]
      abel
    | 1, 1 => simp [b, apply_self_eq_zero hc]

end TauCeti.Topology.CechOne
