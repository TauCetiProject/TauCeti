/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.Quotient
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Collapsing a contractible subspace is a homotopy equivalence

Let `A ⊆ X` be a contractible subspace with the homotopy extension property. Then the quotient
map `X → X / A` collapsing `A` to a point is a homotopy equivalence (Hatcher, Proposition 0.17).
For instance, collapsing a contractible subcomplex of a CW complex, such as an embedded tree in a
graph or in a cell structure of a manifold, does not change the homotopy type.

The quotient `X / A` is not fixed here as a particular construction: the statement applies to
every quotient map `q : X → Y` whose fibres are the points outside `A` and the set `A` itself,
`q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A`. The homotopy equivalence
(`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv`) is `q`
(`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv_apply`), and its homotopy inverse
sends the collapsed point back into `A`
(`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv_symm_apply_mem`).

## Proof

A contraction of `A` is a homotopy from the identity of `A` to a constant map, and the homotopy
extension property extends it to a deformation `f_t` of `X` starting at the identity
(`TauCeti.HasHomotopyExtensionProperty.exists_deformation_of_contractible`). It carries `A` into
`A` at every time and collapses `A` to a point at time one. So `q ∘ f_t` is constant on the fibres
of `q` and descends to a homotopy of `Y` from the identity to `q ∘ g`, where `g : Y → X` is the map
induced by `f_1` (`Topology.IsQuotientMap.liftHomotopy`); and `g ∘ q = f_1` is homotopic to the
identity of `X` through `f_t`.

## Main results

* `TauCeti.HasHomotopyExtensionProperty.exists_deformation_of_contractible`: a contractible
  subspace with the homotopy extension property is collapsed to a point by a deformation of the
  ambient space which keeps it inside itself.
* `TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv`: **collapsing a contractible
  subspace with the homotopy extension property is a homotopy equivalence.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.17.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap unitInterval

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}

/-- **A contractible subspace with the homotopy extension property is collapsed by a deformation
of the ambient space.** If `A ⊆ X` is contractible and has the homotopy extension property, there
is a homotopy `f_t : X → X`, `f_t x = F (t, x)`, starting at the identity, which carries `A` into
`A` at every time and sends all of `A` to a single point `a₀ ∈ A` at time one. -/
theorem HasHomotopyExtensionProperty.exists_deformation_of_contractible
    (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A] :
    ∃ F : C(I × X, X), (∀ x, F (0, x) = x) ∧ (∀ (t : I) (a : X), a ∈ A → F (t, a) ∈ A) ∧
      ∃ a₀ ∈ A, ∀ a ∈ A, F (1, a) = a₀ := by
  obtain ⟨a₀, ⟨H⟩⟩ := id_nullhomotopic A
  -- Extend the contraction of `A`, read as a homotopy of maps into `X`, to a deformation of `X`.
  obtain ⟨F, hF₀, hFA⟩ := hA.exists_extension (ContinuousMap.id X)
    ((subtypeVal A).comp H.toContinuousMap) fun a => by simp
  refine ⟨F, hF₀, fun t a ha => ?_, a₀, a₀.2, fun a ha => ?_⟩
  · rw [hFA t ⟨a, ha⟩]
    exact (H (t, ⟨a, ha⟩)).2
  · rw [hFA 1 ⟨a, ha⟩]
    simp

/-- The deformation of `TauCeti.HasHomotopyExtensionProperty.exists_deformation_of_contractible`,
chosen once. -/
private def collapseDeformation (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A] :
    C(I × X, X) :=
  hA.exists_deformation_of_contractible.choose

private lemma collapseDeformation_zero (hA : HasHomotopyExtensionProperty A)
    [ContractibleSpace A] (x : X) : collapseDeformation hA (0, x) = x :=
  hA.exists_deformation_of_contractible.choose_spec.1 x

private lemma collapseDeformation_mem (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A]
    (t : I) {a : X} (ha : a ∈ A) : collapseDeformation hA (t, a) ∈ A :=
  hA.exists_deformation_of_contractible.choose_spec.2.1 t a ha

private lemma collapseDeformation_one_eq (hA : HasHomotopyExtensionProperty A)
    [ContractibleSpace A] {a b : X} (ha : a ∈ A) (hb : b ∈ A) :
    collapseDeformation hA (1, a) = collapseDeformation hA (1, b) := by
  obtain ⟨a₀, -, h⟩ := hA.exists_deformation_of_contractible.choose_spec.2.2
  exact (h a ha).trans (h b hb).symm

variable {q : C(X, Y)}

/-- The deformation collapsing `A` respects the fibres of a quotient map collapsing `A`. -/
private lemma collapseDeformation_fiber (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A]
    (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) (t : I) {x y : X} (hxy : q x = q y) :
    q (collapseDeformation hA (t, x)) = q (collapseDeformation hA (t, y)) := by
  obtain rfl | ⟨hx, hy⟩ := (hqA x y).1 hxy
  · rfl
  · exact (hqA _ _).2 (.inr ⟨collapseDeformation_mem hA t hx, collapseDeformation_mem hA t hy⟩)

/-- The time-one map of the deformation collapsing `A`. -/
private def collapseTimeOne (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A] :
    C(X, X) :=
  ⟨fun x => collapseDeformation hA (1, x), by fun_prop⟩

private lemma factorsThrough_collapseTimeOne (hA : HasHomotopyExtensionProperty A)
    [ContractibleSpace A] (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) :
    Function.FactorsThrough (collapseTimeOne hA) q := fun x y hxy => by
  obtain rfl | ⟨hx, hy⟩ := (hqA x y).1 hxy
  · rfl
  · exact collapseDeformation_one_eq hA hx hy

/-- The homotopy inverse of the collapse: the time-one map of the deformation collapsing `A`,
which is constant on the fibres of `q`, descended along `q`. -/
private def collapseInverse (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A]
    (hq : Topology.IsQuotientMap ⇑q) (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) :
    C(Y, X) :=
  hq.lift (collapseTimeOne hA) (factorsThrough_collapseTimeOne hA hqA)

private lemma collapseInverse_apply (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A]
    (hq : Topology.IsQuotientMap ⇑q) (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) (x : X) :
    collapseInverse hA hq hqA (q x) = collapseDeformation hA (1, x) :=
  DFunLike.congr_fun (hq.lift_comp _ (factorsThrough_collapseTimeOne hA hqA)) x

/-- **Collapsing a contractible subspace with the homotopy extension property is a homotopy
equivalence** (Hatcher, Proposition 0.17). Let `A ⊆ X` be contractible with the homotopy extension
property, and let `q : X → Y` be a quotient map collapsing exactly `A` to a point:
`q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A`. Then `q` is a homotopy equivalence
(`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv_apply`). -/
def HasHomotopyExtensionProperty.collapseHomotopyEquiv (hA : HasHomotopyExtensionProperty A)
    [ContractibleSpace A] (hq : Topology.IsQuotientMap ⇑q)
    (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) : X ≃ₕ Y :=
  -- The deformation collapsing `A` is a homotopy from the identity of `X` to `g ∘ q`, where `g` is
  -- the descended time-one map.
  let G : (ContinuousMap.id X).Homotopy ((collapseInverse hA hq hqA).comp q) :=
    { toContinuousMap := collapseDeformation hA
      map_zero_left := collapseDeformation_zero hA
      map_one_left := fun x => (collapseInverse_apply hA hq hqA x).symm }
  { toFun := q
    invFun := collapseInverse hA hq hqA
    left_inv := ⟨G.symm⟩
    -- Composed with `q`, the deformation descends to a homotopy of `Y` from the identity to
    -- `q ∘ g`.
    right_inv := ⟨(hq.liftHomotopy ((Homotopy.refl q).comp G)
      (fun t _ _ hxy => collapseDeformation_fiber hA hqA t hxy)
      (g₀ := ContinuousMap.id Y) (g₁ := q.comp (collapseInverse hA hq hqA))
      (fun _ => rfl) fun _ => rfl).symm⟩ }

@[simp]
theorem HasHomotopyExtensionProperty.collapseHomotopyEquiv_apply
    (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A] (hq : Topology.IsQuotientMap ⇑q)
    (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) (x : X) :
    hA.collapseHomotopyEquiv hq hqA x = q x :=
  (rfl)

/-- The homotopy inverse of the collapse `X → X / A` sends the collapsed point into `A`. -/
theorem HasHomotopyExtensionProperty.collapseHomotopyEquiv_symm_apply_mem
    (hA : HasHomotopyExtensionProperty A) [ContractibleSpace A] (hq : Topology.IsQuotientMap ⇑q)
    (hqA : ∀ x y, q x = q y ↔ x = y ∨ x ∈ A ∧ y ∈ A) {a : X} (ha : a ∈ A) :
    (hA.collapseHomotopyEquiv hq hqA).symm (q a) ∈ A :=
  (collapseInverse_apply hA hq hqA a).symm ▸ collapseDeformation_mem hA 1 ha

end TauCeti
