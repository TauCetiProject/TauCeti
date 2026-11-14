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
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

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

No finiteness of the index type and no covering hypothesis is needed.

## Main definitions

* `TauCeti.Topology.CechOne.d₀`, `TauCeti.Topology.CechOne.d₁`: the Čech differentials in degrees
  zero and one, on families of sections over the members and their pairwise intersections.
* `TauCeti.Topology.CechOne.cocycles P U`: the submodule of one-cocycles.
* `TauCeti.Topology.CechOne.coboundary P U`: the coboundary map from zero-cochains to cocycles.
* `TauCeti.Topology.CechOne.toHomology P U`: the class of a cocycle in the degree one cohomology
  of Mathlib's Čech complex.
* `TauCeti.Topology.CechOne.homologyLinearEquiv P U`: cocycles modulo coboundaries are isomorphic
  to that cohomology.
* `TauCeti.Topology.CechOne.cocyclesMap φ` and `TauCeti.Topology.CechOne.cocyclesMapOfHom α`: the
  maps of cocycles induced by a refinement `φ` and by a morphism of presheaves `α`.

## Main results

* `TauCeti.Topology.CechOne.apply_self_eq_zero` and `TauCeti.Topology.CechOne.apply_swap`: a
  cocycle vanishes on the diagonal and is alternating.
* `TauCeti.Topology.CechOne.toHomology_surjective` and
  `TauCeti.Topology.CechOne.ker_toHomology`: every class is represented by a cocycle, and the
  cocycles representing zero are the coboundaries.
* `TauCeti.Topology.CechOne.toHomology_cocyclesMap`: compatibility with the map on Čech
  cohomology induced by a refinement (`TauCeti.CategoryTheory.cechComplexHomologyMap`).
* `TauCeti.Topology.CechOne.toHomology_cocyclesMapOfHom`: compatibility with the map induced by a
  morphism of presheaves.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_iff`: the degree one cohomology vanishes if
  and only if every cocycle is a coboundary.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_fin_two_iff`: for a family of two opens, the
  degree one cohomology vanishes if and only if every section over `U 0 ∩ U 1` is a difference of
  restrictions; this is the elementwise description of
  `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective` in
  degree one.
* `TauCeti.Topology.CechOne.subsingleton_homology_one_of_le`: if one member contains all the
  others, for instance for a constant family, the degree one cohomology vanishes.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §12.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology.CechOne

variable {X : TopCat.{u}} {R : Type u} [Ring R] (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
  {ι : Type u} (U : ι → Opens X)

/-! ### Cochains, cocycles and coboundaries -/

/-- The Čech differential on zero-cochains: `(d₀ b) i j = b j - b i` on `U i ∩ U j`. -/
@[expose]
def d₀ : (∀ i, P.obj (op (U i))) →ₗ[R] ∀ i j, P.obj (op (U i ⊓ U j)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (P.map (homOfLE inf_le_right).op).hom ∘ₗ LinearMap.proj j -
      (P.map (homOfLE inf_le_left).op).hom ∘ₗ LinearMap.proj i

@[simp]
theorem d₀_apply (b : ∀ i, P.obj (op (U i))) (i j : ι) :
    d₀ P U b i j = P.map (homOfLE inf_le_right).op (b j) - P.map (homOfLE inf_le_left).op (b i) :=
  rfl

/-- The Čech differential on one-cochains: `(d₁ c) i j k = c j k - c i k + c i j` on
`U i ∩ U j ∩ U k`. -/
@[expose]
def d₁ : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ i j k, P.obj (op (U i ⊓ U j ⊓ U k)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op).hom ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj j) -
      (P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj i) +
      (P.map (homOfLE inf_le_left).op).hom ∘ₗ (LinearMap.proj j ∘ₗ LinearMap.proj i)

@[simp]
theorem d₁_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (i j k : ι) :
    d₁ P U c i j k =
      P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (c j k) -
        P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (c i k) +
        P.map (homOfLE inf_le_left).op (c i j) :=
  rfl

/-- Restrictions compose. -/
@[simp]
theorem map_homOfLE_map_homOfLE_apply {V W Y : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ Y)
    (y : P.obj (op Y)) :
    P.map (homOfLE h₁).op (P.map (homOfLE h₂).op y) = P.map (homOfLE (h₁.trans h₂)).op y := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, homOfLE_comp]

/-- Restriction from an open to itself is the identity. -/
theorem map_homOfLE_self_apply {V : Opens X} (h : V ≤ V) (y : P.obj (op V)) :
    P.map (homOfLE h).op y = y := by
  rw [show homOfLE h = 𝟙 V from rfl, op_id, P.map_id, ModuleCat.id_apply]

/-- In the thin category `Opens X`, two composites of restrictions with the same source and
target agree. -/
private lemma map_map_apply {V W Y : Opens X} (f : V ⟶ W) (g : W ⟶ Y) (h : V ⟶ Y)
    (y : P.obj (op Y)) : P.map f.op (P.map g.op y) = P.map h.op y := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, Subsingleton.elim (f ≫ g) h]

/-- The differential of a coboundary vanishes. -/
@[simp]
theorem d₁_d₀ (b : ∀ i, P.obj (op (U i))) : d₁ P U (d₀ P U b) = 0 := by
  funext i j k
  simp only [d₁_apply, d₀_apply, map_sub, map_homOfLE_map_homOfLE_apply, Pi.zero_apply]
  abel

/-- The one-cocycles: one-cochains whose alternating sum vanishes on every triple
intersection. -/
@[expose]
def cocycles : Submodule R (∀ i j, P.obj (op (U i ⊓ U j))) :=
  LinearMap.ker (d₁ P U)

theorem mem_cocycles_iff {c : ∀ i j, P.obj (op (U i ⊓ U j))} :
    c ∈ cocycles P U ↔ ∀ i j k,
      P.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (c j k) -
        P.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (c i k) +
        P.map (homOfLE inf_le_left).op (c i j) = 0 := by
  simp only [cocycles, LinearMap.mem_ker, funext_iff, d₁_apply, Pi.zero_apply]

variable {P U} in
/-- The cocycle identity for `(i, j, k)`, restricted to any open contained in
`U i ∩ U j ∩ U k`. -/
theorem map_add_map_sub_map_eq_zero {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles P U)
    {i j k : ι} {W : Opens X} (hW : W ≤ U i ⊓ U j ⊓ U k) :
    P.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))).op (c j k) -
        P.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))).op
          (c i k) +
        P.map (homOfLE (hW.trans inf_le_left)).op (c i j) = 0 := by
  have h := congrArg (P.map (homOfLE hW).op) ((mem_cocycles_iff P U).1 hc i j k)
  simpa only [map_add, map_sub, map_zero, map_homOfLE_map_homOfLE_apply] using h

variable {P U} in
/-- A cocycle vanishes on the diagonal. -/
theorem apply_self_eq_zero {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles P U) (i : ι) :
    c i i = 0 := by
  have h := map_add_map_sub_map_eq_zero hc (i := i) (j := i) (k := i) (W := U i ⊓ U i)
    (le_inf le_rfl inf_le_left)
  simpa only [map_homOfLE_self_apply, sub_self, zero_add] using h

variable {P U} in
/-- A cocycle is alternating. -/
theorem apply_swap {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles P U) (i j : ι) :
    c j i = -P.map (homOfLE (le_inf inf_le_right inf_le_left)).op (c i j) := by
  have h := map_add_map_sub_map_eq_zero hc (i := i) (j := j) (k := i) (W := U j ⊓ U i)
    (le_inf (le_inf inf_le_right inf_le_left) inf_le_right)
  rw [map_homOfLE_self_apply, apply_self_eq_zero hc, map_zero, sub_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The coboundary map, from zero-cochains to one-cocycles. -/
@[expose]
def coboundary : (∀ i, P.obj (op (U i))) →ₗ[R] cocycles P U :=
  (d₀ P U).codRestrict _ fun b ↦ LinearMap.mem_ker.2 (d₁_d₀ P U b)

@[simp]
theorem coboundary_apply_coe (b : ∀ i, P.obj (op (U i))) :
    (coboundary P U b : ∀ i j, P.obj (op (U i ⊓ U j))) = d₀ P U b :=
  rfl

/-! ### Comparison with Mathlib's Čech complex

The degree `n` term of `(cechComplexFunctor U).obj P` is a categorical product of `R`-modules,
whose elements are determined by their coordinates (`coord`). Its factors are the values of `P`
on categorical products of members, which in `Opens X` are the intersections. The maps
`toCochains₀`, `toCochains₁` and `toCochains₂` read off the restrictions of the coordinates indexed
by `![i]`, `![i, j]` and `![i, j, k]`; in degrees zero and one, `ofCochains₀` and `ofCochains₁`
go back. -/

/-- Mathlib's Čech complex of `P` for `U`. -/
private abbrev K : CochainComplex (ModuleCat.{u} R) ℕ := (cechComplexFunctor U).obj P

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
    x = y := by
  let e := ModuleCat.piIsoPi fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))
  have he (z : (K P U).X n) : e.hom.hom z = fun a ↦ coord P U a z := funext fun a ↦
    congr($(ModuleCat.piIsoPi_hom_ker_subtype
      (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a).hom z)
  have hinj : Function.Injective e.hom.hom := fun z w hzw ↦ by
    simpa using congr(e.inv.hom $hzw)
  exact hinj ((he x).trans ((funext h).trans (he y).symm))

/-- Restrictions from coordinates indexed by equal tuples agree. -/
private lemma map_coord_eq {n : ℕ} {b b' : Fin (n + 1) → ι} (h : b = b') {W : Opens X}
    (f : W ⟶ ∏ᶜ fun j ↦ U (b j)) (f' : W ⟶ ∏ᶜ fun j ↦ U (b' j)) (x : (K P U).X n) :
    P.map f.op (coord P U b x) = P.map f'.op (coord P U b' x) := by
  subst h
  rw [Subsingleton.elim f f']

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
  rfl

private lemma toCochains₁_apply (x : (K P U).X 1) (i j : ι) :
    toCochains₁ P U x i j =
      P.map (liftHom U ![i, j] (Fin.forall_fin_two.2 ⟨inf_le_left, inf_le_right⟩) :
        U i ⊓ U j ⟶ _).op (coord P U ![i, j] x) :=
  rfl

private lemma toCochains₂_apply (x : (K P U).X 2) (i j k : ι) :
    toCochains₂ P U x i j k =
      P.map (liftHom U ![i, j, k] (Fin.forall_fin_succ.2
        ⟨inf_le_left.trans inf_le_left, Fin.forall_fin_two.2
          ⟨inf_le_left.trans inf_le_right, inf_le_right⟩⟩) : U i ⊓ U j ⊓ U k ⟶ _).op
        (coord P U ![i, j, k] x) :=
  rfl

private lemma coord_ofCochains₀ (b : ∀ i, P.obj (op (U i))) (a : Fin 1 → ι) :
    coord P U a (ofCochains₀ P U b) = P.map (homOfLE (le_π U a 0)).op (b (a 0)) :=
  coord_mk P U _ a

private lemma coord_ofCochains₁ (c : ∀ i j, P.obj (op (U i ⊓ U j))) (a : Fin 2 → ι) :
    coord P U a (ofCochains₁ P U c) =
      P.map (homOfLE (le_inf (le_π U a 0) (le_π U a 1))).op (c (a 0) (a 1)) :=
  coord_mk P U _ a

private lemma map_id_apply {V : Opens X} (f : V ⟶ V) (y : P.obj (op V)) : P.map f.op y = y := by
  rw [Subsingleton.elim f (𝟙 V), op_id, P.map_id, ModuleCat.id_apply]

private lemma toCochains₀_ofCochains₀ (b : ∀ i, P.obj (op (U i))) :
    toCochains₀ P U (ofCochains₀ P U b) = b := by
  funext i
  rw [toCochains₀_apply, coord_ofCochains₀, map_map_apply P _ _ (𝟙 _), map_id_apply]

private lemma toCochains₁_ofCochains₁ (c : ∀ i j, P.obj (op (U i ⊓ U j))) :
    toCochains₁ P U (ofCochains₁ P U c) = c := by
  funext i j
  rw [toCochains₁_apply, coord_ofCochains₁]
  exact (map_map_apply P _ _ (𝟙 _) _).trans (map_id_apply P _ _)

private lemma ofCochains₁_toCochains₁ (x : (K P U).X 1) :
    ofCochains₁ P U (toCochains₁ P U x) = x := by
  refine ext_coord P U fun a ↦ ?_
  rw [coord_ofCochains₁, toCochains₁_apply, map_map_apply P _ _ (liftHom U ![a 0, a 1]
    fun j ↦ by fin_cases j <;> exact le_π U a _)]
  exact (map_coord_eq P U (b' := a) (funext fun j ↦ by fin_cases j <;> rfl) _ (𝟙 _) x).trans
    (map_id_apply P _ _)

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
  rw [map_zero, map_map_apply P _ _ (liftHom U ![a 0, a 1, a 2] fun j ↦ by
    fin_cases j <;> exact le_π U a _)] at h'
  rw [map_zero, ← h']
  exact ((map_coord_eq P U (b' := a) (funext fun j ↦ by fin_cases j <;> rfl) _ (𝟙 _) x).trans
    (map_id_apply P _ _)).symm

/-- Restrictions of restrictions of coordinates indexed by equal tuples agree. -/
private lemma map_map_coord_eq {n : ℕ} {b b' : Fin (n + 1) → ι} (h : b = b') {W W₁ W₂ : Opens X}
    (f : W ⟶ W₁) (g : W₁ ⟶ ∏ᶜ fun j ↦ U (b j)) (f' : W ⟶ W₂) (g' : W₂ ⟶ ∏ᶜ fun j ↦ U (b' j))
    (x : (K P U).X n) :
    P.map f.op (P.map g.op (coord P U b x)) = P.map f'.op (P.map g'.op (coord P U b' x)) := by
  subst h
  rw [map_map_apply P f g (f ≫ g), map_map_apply P f' g' (f ≫ g)]

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
    toCochains₁ P U ((K P U).d 0 1 y) = d₀ P U (toCochains₀ P U y) := by
  funext i j
  rw [toCochains₁_apply, coord_d, Fin.sum_univ_two, d₀_apply, toCochains₀_apply,
    toCochains₀_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    ← sub_eq_add_neg, map_sub]
  congr 1 <;> refine map_map_coord_eq P U ?_ _ _ _ _ _ <;> funext t <;> fin_cases t <;> rfl

private lemma toCochains₂_d (x : (K P U).X 1) :
    toCochains₂ P U ((K P U).d 1 2 x) = d₁ P U (toCochains₁ P U x) := by
  funext i j k
  rw [toCochains₂_apply, coord_d, Fin.sum_univ_three, d₁_apply, toCochains₁_apply,
    toCochains₁_apply, toCochains₁_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two,
    map_add, ← sub_eq_add_neg, map_sub, neg_one_sq]
  congr 1
  · congr 1 <;> refine map_map_coord_eq P U ?_ _ _ _ _ _ <;> funext t <;> fin_cases t <;> rfl
  · refine map_map_coord_eq P U ?_ _ _ _ _ _
    funext t
    fin_cases t <;> rfl

/-! ### Cocycles compute degree one Čech cohomology -/

/-- The inclusion of the cocycles into the Čech one-cochains. -/
private def cocyclesι : ModuleCat.of R (cocycles P U) ⟶ (K P U).X 1 :=
  ModuleCat.ofHom (ofCochains₁ P U ∘ₗ (cocycles P U).subtype)

private lemma d_ofCochains₁ {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles P U) :
    (K P U).d 1 2 (ofCochains₁ P U c) = 0 :=
  toCochains₂_injective P U (by rw [toCochains₂_d, toCochains₁_ofCochains₁, map_zero]; exact hc)

private lemma toCochains₁_mem {w : (K P U).X 1} (hw : (K P U).d 1 2 w = 0) :
    toCochains₁ P U w ∈ cocycles P U := by
  rw [cocycles, LinearMap.mem_ker, ← toCochains₂_d, hw, map_zero]

/-- The Čech one-cycle defined by a cocycle. -/
private def toCycles : ModuleCat.of R (cocycles P U) ⟶ (K P U).cycles 1 :=
  (K P U).liftCycles (cocyclesι P U) 2 (by simp) <| by
    ext c
    exact d_ofCochains₁ P U c.2

private lemma iCycles_toCycles (c : cocycles P U) :
    (K P U).iCycles 1 (toCycles P U c) = ofCochains₁ P U c :=
  ConcreteCategory.congr_hom ((K P U).liftCycles_i (cocyclesι P U) 2 (by simp) _) c

/-- The class in degree one Čech cohomology of a one-cocycle. -/
def toHomology : cocycles P U →ₗ[R] ((cechComplexFunctor U).obj P).homology 1 :=
  (toCycles P U ≫ (K P U).homologyπ 1).hom

private lemma toHomology_apply (c : cocycles P U) :
    toHomology P U c = (K P U).homologyπ 1 (toCycles P U c) :=
  rfl

/-- The class of a cocycle is the class of any Čech one-cycle with the same restrictions. -/
private lemma toHomology_eq (c : cocycles P U) (z : (K P U).cycles 1)
    (hz : toCochains₁ P U ((K P U).iCycles 1 z) = c) :
    toHomology P U c = (K P U).homologyπ 1 z := by
  rw [toHomology_apply]
  congr 1
  refine (ModuleCat.mono_iff_injective ((K P U).iCycles 1)).1 inferInstance ?_
  rw [iCycles_toCycles, ← hz, ofCochains₁_toCochains₁]

private lemma d_iCycles (z : (K P U).cycles 1) : (K P U).d 1 2 ((K P U).iCycles 1 z) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
  rfl

/-- Every degree one Čech cohomology class is the class of a cocycle. -/
theorem toHomology_surjective : Function.Surjective (toHomology P U) := by
  intro h
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((K P U).homologyπ 1)).1 inferInstance h
  exact ⟨⟨_, toCochains₁_mem P U (d_iCycles P U z)⟩, toHomology_eq P U _ z rfl⟩

/-- A cocycle has zero class in degree one Čech cohomology if and only if it is a
coboundary. -/
theorem ker_toHomology : LinearMap.ker (toHomology P U) = LinearMap.range (coboundary P U) := by
  ext c
  constructor
  · intro hc
    have hT := (ShortComplex.mk ((K P U).toCycles 0 1) ((K P U).homologyπ 1)
      (by simp)).exact_of_g_is_cokernel ((K P U).homologyIsCokernel 0 1 (by simp))
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hT (toCycles P U c) hc
    refine ⟨toCochains₀ P U y, Subtype.ext ?_⟩
    have hy' := congrArg ((K P U).iCycles 1) hy
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, iCycles_toCycles] at hy'
    rw [coboundary_apply_coe, ← toCochains₁_d, hy', toCochains₁_ofCochains₁]
  · rintro ⟨b, rfl⟩
    rw [LinearMap.mem_ker, toHomology_eq P U _ ((K P U).toCycles 0 1 (ofCochains₀ P U b))]
    · rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
      rfl
    · rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, toCochains₁_d,
        toCochains₀_ofCochains₀]
      rfl

/-- **Degree one Čech cohomology as cocycles modulo coboundaries.** -/
@[expose]
def homologyLinearEquiv :
    (cocycles P U ⧸ LinearMap.range (coboundary P U)) ≃ₗ[R]
      ((cechComplexFunctor U).obj P).homology 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_toHomology P U).symm).trans
    ((toHomology P U).quotKerEquivOfSurjective (toHomology_surjective P U))

@[simp]
theorem homologyLinearEquiv_mk (c : cocycles P U) :
    homologyLinearEquiv P U (Submodule.Quotient.mk c) = toHomology P U c :=
  rfl

/-! ### Naturality -/

section Refinement

variable {P U} {κ : Type u} {V : κ → Opens X}
  (φ : FormalCoproduct.mk _ V ⟶ FormalCoproduct.mk _ U)

/-- Restriction of one-cochains along a refinement `φ`: the component at `(k, l)` is the
restriction of the component at `(φ.f k, φ.f l)`. -/
@[expose]
def cochainsMap : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ k l, P.obj (op (V k ⊓ V l)) :=
  LinearMap.pi fun k ↦ LinearMap.pi fun l ↦
    (P.map (homOfLE (inf_le_inf (leOfHom (φ.φ k)) (leOfHom (φ.φ l)))).op).hom ∘ₗ
      (LinearMap.proj (φ.f l) ∘ₗ LinearMap.proj (φ.f k))

@[simp]
theorem cochainsMap_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (k l : κ) :
    cochainsMap φ c k l =
      P.map (homOfLE (inf_le_inf (leOfHom (φ.φ k)) (leOfHom (φ.φ l)))).op (c (φ.f k) (φ.f l)) :=
  rfl

private lemma toCochains₁_cechComplexMap (x : (K P U).X 1) :
    toCochains₁ P V ((TauCeti.CategoryTheory.cechComplexMap P φ).f 1 x) =
      cochainsMap φ (toCochains₁ P U x) := by
  funext k l
  have h := congr($(TauCeti.CategoryTheory.cechComplexMap_f_π P φ 1 ![k, l]).hom x)
  rw [toCochains₁_apply, cochainsMap_apply, toCochains₁_apply]
  refine (congrArg _ h).trans ?_
  refine map_map_coord_eq P U ?_ _ _ _ _ x
  funext t
  fin_cases t <;> rfl

theorem cochainsMap_mem_cocycles {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : c ∈ cocycles P U) :
    cochainsMap φ c ∈ cocycles P V := by
  rw [← toCochains₁_ofCochains₁ P U c, ← toCochains₁_cechComplexMap]
  refine toCochains₁_mem P V ?_
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm, ConcreteCategory.comp_apply,
    d_ofCochains₁ P U hc, map_zero]

/-- The map of cocycles induced by a refinement `φ`. -/
@[expose]
def cocyclesMap : cocycles P U →ₗ[R] cocycles P V :=
  (cochainsMap φ).restrict fun _ hc ↦ cochainsMap_mem_cocycles φ hc

@[simp]
theorem cocyclesMap_apply_coe (c : cocycles P U) :
    (cocyclesMap φ c : ∀ k l, P.obj (op (V k ⊓ V l))) = cochainsMap φ c :=
  rfl

/-- The class of the restriction of a cocycle along a refinement `φ` is the image of its class
under the map on Čech cohomology induced by `φ`. -/
theorem toHomology_cocyclesMap (c : cocycles P U) :
    toHomology P V (cocyclesMap φ c) =
      HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechComplexMap P φ) 1
        (toHomology P U c) := by
  rw [toHomology_eq P V _ (HomologicalComplex.cyclesMap
    (TauCeti.CategoryTheory.cechComplexMap P φ) 1 (toCycles P U c)), toHomology_apply]
  · have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (TauCeti.CategoryTheory.cechComplexMap P φ) 1) (toCycles P U c)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h.symm
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_toCycles, toCochains₁_cechComplexMap, toCochains₁_ofCochains₁, cocyclesMap_apply_coe]

end Refinement

section Presheaf

variable {P} {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R} (α : P ⟶ Q)

/-- The map of one-cochains induced by a morphism of presheaves. -/
@[expose]
def cochainsMapOfHom : (∀ i j, P.obj (op (U i ⊓ U j))) →ₗ[R] ∀ i j, Q.obj (op (U i ⊓ U j)) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (α.app (op (U i ⊓ U j))).hom ∘ₗ (LinearMap.proj j ∘ₗ LinearMap.proj i)

@[simp]
theorem cochainsMapOfHom_apply (c : ∀ i j, P.obj (op (U i ⊓ U j))) (i j : ι) :
    cochainsMapOfHom U α c i j = α.app (op (U i ⊓ U j)) (c i j) :=
  rfl

private lemma toCochains₁_cechComplexFunctor_map (x : (K P U).X 1) :
    toCochains₁ Q U (((cechComplexFunctor U).map α).f 1 x) =
      cochainsMapOfHom U α (toCochains₁ P U x) := by
  funext i j
  have h := congr($(TauCeti.CategoryTheory.cechComplexFunctor_map_f_π U P α 1 ![i, j]).hom x)
  rw [toCochains₁_apply, cochainsMapOfHom_apply, toCochains₁_apply]
  exact (congrArg _ h).trans (ConcreteCategory.congr_hom (α.naturality _) _).symm

theorem cochainsMapOfHom_mem_cocycles {c : ∀ i j, P.obj (op (U i ⊓ U j))}
    (hc : c ∈ cocycles P U) : cochainsMapOfHom U α c ∈ cocycles Q U := by
  rw [← toCochains₁_ofCochains₁ P U c, ← toCochains₁_cechComplexFunctor_map]
  refine toCochains₁_mem Q U ?_
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm, ConcreteCategory.comp_apply,
    d_ofCochains₁ P U hc, map_zero]

/-- The map of cocycles induced by a morphism of presheaves. -/
@[expose]
def cocyclesMapOfHom : cocycles P U →ₗ[R] cocycles Q U :=
  (cochainsMapOfHom U α).restrict fun _ hc ↦ cochainsMapOfHom_mem_cocycles U α hc

@[simp]
theorem cocyclesMapOfHom_apply_coe (c : cocycles P U) :
    (cocyclesMapOfHom U α c : ∀ i j, Q.obj (op (U i ⊓ U j))) = cochainsMapOfHom U α c :=
  rfl

/-- The class of the image of a cocycle under a morphism of presheaves `α` is the image of its
class under the map on Čech cohomology induced by `α`. -/
theorem toHomology_cocyclesMapOfHom (c : cocycles P U) :
    toHomology Q U (cocyclesMapOfHom U α c) =
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map α) 1 (toHomology P U c) := by
  rw [toHomology_eq Q U _ (HomologicalComplex.cyclesMap ((cechComplexFunctor U).map α) 1
    (toCycles P U c)), toHomology_apply]
  · have h := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality ((cechComplexFunctor U).map α) 1) (toCycles P U c)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h.symm
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_toCycles, toCochains₁_cechComplexFunctor_map, toCochains₁_ofCochains₁,
    cocyclesMapOfHom_apply_coe]

end Presheaf

/-! ### Checks -/

/-- The degree one Čech cohomology vanishes if and only if every cocycle is a coboundary. -/
theorem subsingleton_homology_one_iff :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) ↔
      ∀ c ∈ cocycles P U, ∃ b, d₀ P U b = c := by
  constructor
  · intro _ c hc
    obtain ⟨b, hb⟩ : ⟨c, hc⟩ ∈ LinearMap.range (coboundary P U) := by
      rw [← ker_toHomology, LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    exact ⟨b, congrArg Subtype.val hb⟩
  · intro h
    suffices ∀ x : ((cechComplexFunctor U).obj P).homology 1, x = 0 from
      ⟨fun x y ↦ (this x).trans (this y).symm⟩
    intro x
    obtain ⟨c, rfl⟩ := toHomology_surjective P U x
    obtain ⟨b, hb⟩ := h c c.2
    rw [← LinearMap.mem_ker, ker_toHomology]
    exact ⟨b, Subtype.ext hb⟩

/-- If one member of the family contains all the others, the degree one Čech cohomology
vanishes: a cocycle `c` is the coboundary of the restrictions of `c i₀ i` to `U i`. -/
theorem subsingleton_homology_one_of_le (i₀ : ι) (h : ∀ i, U i ≤ U i₀) :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) := by
  refine (subsingleton_homology_one_iff P U).2 fun c hc ↦
    ⟨fun i ↦ P.map (homOfLE (le_inf (h i) le_rfl)).op (c i₀ i), funext fun i ↦ funext fun j ↦ ?_⟩
  have hc' := map_add_map_sub_map_eq_zero hc (i := i₀) (j := i) (k := j) (W := U i ⊓ U j)
    (le_inf (le_inf (inf_le_left.trans (h i)) inf_le_left) inf_le_right)
  rw [map_homOfLE_self_apply] at hc'
  rw [d₀_apply, map_homOfLE_map_homOfLE_apply, map_homOfLE_map_homOfLE_apply]
  rw [← sub_eq_zero, ← neg_eq_zero, ← hc']
  abel

/-- **Check.** A constant family has vanishing degree one Čech cohomology. -/
theorem subsingleton_homology_one_const [Nonempty ι] (W : Opens X) :
    Subsingleton (((cechComplexFunctor fun _ : ι ↦ W).obj P).homology 1) :=
  subsingleton_homology_one_of_le P _ (Classical.arbitrary ι) fun _ ↦ le_rfl

/-- **Check.** For a family of two opens `U 0` and `U 1`, the degree one Čech cohomology vanishes
if and only if every section over `U 0 ∩ U 1` is the difference of the restrictions of a section
over `U 0` and a section over `U 1`. This is the degree one part of
`TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective`. The
family is indexed by `ULift (Fin 2)`, since the index type lives in the universe of the
modules. -/
theorem subsingleton_homology_one_fin_two_iff (U : ULift.{u} (Fin 2) → Opens X) :
    Subsingleton (((cechComplexFunctor U).obj P).homology 1) ↔
      Function.Surjective fun x : P.obj (op (U ⟨0⟩)) × P.obj (op (U ⟨1⟩)) ↦
        P.map (homOfLE inf_le_left : U ⟨0⟩ ⊓ U ⟨1⟩ ⟶ U ⟨0⟩).op x.1 -
          P.map (homOfLE inf_le_right : U ⟨0⟩ ⊓ U ⟨1⟩ ⟶ U ⟨1⟩).op x.2 := by
  rw [subsingleton_homology_one_iff]
  constructor
  · intro h s
    let c : ∀ i j, P.obj (op (U i ⊓ U j)) := fun
      | ⟨0⟩, ⟨0⟩ => 0
      | ⟨0⟩, ⟨1⟩ => s
      | ⟨1⟩, ⟨0⟩ => -P.map (homOfLE (le_inf inf_le_right inf_le_left)).op s
      | ⟨1⟩, ⟨1⟩ => 0
    have hc : c ∈ cocycles P U := by
      rw [mem_cocycles_iff]
      rintro ⟨i⟩ ⟨j⟩ ⟨k⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [c, map_homOfLE_map_homOfLE_apply]
    obtain ⟨b, hb⟩ := h c hc
    refine ⟨(-b ⟨0⟩, -b ⟨1⟩), ?_⟩
    have h01 : P.map (homOfLE inf_le_right).op (b ⟨1⟩) - P.map (homOfLE inf_le_left).op (b ⟨0⟩) =
        s :=
      congrFun (congrFun hb ⟨0⟩) ⟨1⟩
    simp only [map_neg, ← h01]
    abel
  · intro h c hc
    obtain ⟨x, hx⟩ := h (c ⟨0⟩ ⟨1⟩)
    let b : ∀ i, P.obj (op (U i)) := fun
      | ⟨0⟩ => -x.1
      | ⟨1⟩ => -x.2
    refine ⟨b, funext fun i ↦ funext fun j ↦ ?_⟩
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    match i, j with
    | 0, 0 => simp [b, apply_self_eq_zero hc]
    | 0, 1 =>
      simp only [d₀_apply, b, map_neg, ← hx]
      abel
    | 1, 0 =>
      rw [apply_swap hc, ← hx]
      simp [b, map_homOfLE_map_homOfLE_apply]
      abel
    | 1, 1 => simp [b, apply_self_eq_zero hc]

end TauCeti.Topology.CechOne
