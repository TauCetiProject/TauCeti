/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Equiv.Pi
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Pi.Basic

/-!
# External products of families of representations

For representations `ρ i` of monoids `G i` on modules `V i`, the **external product**
`Representation.externalPi ρ` is the representation of the product group `∀ i, G i` on
`∀ i, V i` in which `g` acts on the `i`-th coordinate by `ρ i (g i)`. Restricted along the
diagonal of a single group it is the product `Representation.pi` of representations of that group
(`Representation.externalPi_comp_diag`), and a single factor `G i` acts on the `i`-th coordinate
alone (`Representation.externalPi_mulSingle`).

For a finite set `I` of indices this is the representation of `Γ_I = ∏_(α ∈ I) Γ_α` on
`E_I = ⊕_(α ∈ I) E_α` that carries the obstruction spaces of an implicit atlas, in the sense of
Pardon. The file provides the maps between these representations that the atlas axioms use:

* the coordinate projections `E_I → E_α`, equivariant for `Γ_I` acting on `E_α` through `Γ_α`;
* for finite sets `s ⊆ t`, the restriction `E_t → E_s` and the extension by zero `E_s → E_t`,
  equivariant for `Γ_t` acting on `E_s` through the restriction `Γ_t → Γ_s`; restriction after
  extension is the identity, and both are compatible with composition;
* for disjoint `s` and `t`, the identification of `E_(s ∪ t)` with `E_s × E_t`, equivariant for
  `Γ_s × Γ_t ≃ Γ_(s ∪ t)`; under it the projections are the restrictions and the inclusions of the
  factors are the extensions by zero;
* for an equivalence `e : ι' ≃ ι` of index types, the identification of the external product of
  `ρ` with that of the relabelled family `ρ ∘ e`, compatible with composition of equivalences.

The disjoint-union identification is associative on underlying functions
(`Equiv.restrict₂_piFinsetUnion_assoc`).

## Main definitions

* `Representation.externalPi`: the external product of a family of representations.
* `Representation.externalPiProj`: the equivariant coordinate projection.
* `Representation.externalPiRestrict₂`: the equivariant restriction to a smaller finite set.
* `Representation.externalPiExtend`: the equivariant extension by zero to a larger finite set.
* `Representation.externalPiUnion`: the equivariant splitting over a disjoint union.
* `Representation.externalPiCongrLeft`: the equivariant relabelling of the index type.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition 3.1.1.
-/

public section

namespace Representation

variable {k ι : Type*} [CommSemiring k] {G : ι → Type*} [∀ i, Monoid (G i)] {V : ι → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k (G i) (V i))

/-- **The external product** of a family of representations `ρ i` of `G i` on `V i`: the
representation of `∀ i, G i` on `∀ i, V i` in which `g` acts on the `i`-th coordinate by
`ρ i (g i)`. -/
noncomputable def externalPi : Representation k (∀ i, G i) (∀ i, V i) :=
  pi fun i ↦ (ρ i).comp (Pi.evalMonoidHom G i)

/-- `g` acts on the `i`-th coordinate by `ρ i (g i)`. -/
@[simp]
theorem externalPi_apply (g : ∀ i, G i) (x : ∀ i, V i) (i : ι) :
    externalPi ρ g x i = ρ i (g i) (x i) := by
  simp [externalPi]

/-- **The product of representations of one group is the diagonal restriction of the external
product.** -/
@[simp]
theorem externalPi_comp_diag {H : Type*} [Monoid H] (σ : ∀ i, Representation k H (V i)) :
    (externalPi σ).comp (MonoidHom.pi fun _ ↦ MonoidHom.id H) = pi σ := by
  ext
  simp

/-- An element of the single factor `G i` acts on the `i`-th coordinate alone. -/
theorem externalPi_mulSingle [DecidableEq ι] (i : ι) (g : G i) (x : ∀ i, V i) :
    externalPi ρ (Pi.mulSingle i g) x = Function.update x i (ρ i g (x i)) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- **The coordinate projection** `(∀ i, V i) → V i`, equivariant for `∀ i, G i` acting on `V i`
through its factor `G i`. -/
noncomputable def externalPiProj (i : ι) :
    IntertwiningMap (externalPi ρ) ((ρ i).comp (Pi.evalMonoidHom G i)) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (LinearMap.proj i) fun _ _ ↦ by simp

/-- `externalPiProj ρ i` takes the `i`-th coordinate. -/
@[simp]
theorem externalPiProj_apply (i : ι) (x : ∀ i, V i) : externalPiProj ρ i x = x i :=
  (rfl)

/-! ### Products indexed by finite sets -/

section Finset

variable {s t u : Finset ι}

/-- **The restriction** from the coordinates in `t` to those in `s ⊆ t`, equivariant for the
product over `t` acting on the product over `s` through the restriction of groups. -/
noncomputable def externalPiRestrict₂ (h : s ⊆ t) :
    IntertwiningMap (externalPi fun i : t ↦ ρ i)
      ((externalPi fun i : s ↦ ρ i).comp (Finset.restrict₂MonoidHom G h)) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.pi fun i : s ↦ LinearMap.proj (⟨i, h i.property⟩ : t)) fun _ _ ↦ funext fun _ ↦ by
        simp

/-- `externalPiRestrict₂ ρ h` restricts a family to the smaller finite set. -/
@[simp]
theorem externalPiRestrict₂_apply (h : s ⊆ t) (x : ∀ i : t, V i) :
    externalPiRestrict₂ ρ h x = Finset.restrict₂ h x :=
  (rfl)

variable [DecidableEq ι]

/-- **The extension by zero** from the coordinates in `s` to those in `t ⊇ s`, equivariant for
the product over `t` acting on the product over `s` through the restriction of groups. -/
noncomputable def externalPiExtend (h : s ⊆ t) :
    IntertwiningMap ((externalPi fun i : s ↦ ρ i).comp (Finset.restrict₂MonoidHom G h))
      (externalPi fun i : t ↦ ρ i) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.pi fun j : t ↦ if hj : (j : ι) ∈ s then LinearMap.proj (⟨j, hj⟩ : s) else 0)
    fun g x ↦ funext fun j ↦ by
      by_cases hj : (j : ι) ∈ s <;> simp [hj]

/-- The extension by zero takes the value of `x` at the indices of `s` and vanishes elsewhere. -/
theorem externalPiExtend_apply (h : s ⊆ t) (x : ∀ i : s, V i) (j : t) :
    externalPiExtend ρ h x j = if hj : (j : ι) ∈ s then x ⟨j, hj⟩ else 0 := by
  by_cases hj : (j : ι) ∈ s <;> simp [externalPiExtend, hj]

/-- The extension by zero takes the value of `x` at an index of `s`. -/
@[simp]
theorem externalPiExtend_apply_of_mem (h : s ⊆ t) (x : ∀ i : s, V i) {j : t}
    (hj : (j : ι) ∈ s) : externalPiExtend ρ h x j = x ⟨j, hj⟩ := by
  simp [externalPiExtend_apply, hj]

/-- The extension by zero vanishes at an index outside `s`. -/
@[simp]
theorem externalPiExtend_apply_of_notMem (h : s ⊆ t) (x : ∀ i : s, V i) {j : t}
    (hj : (j : ι) ∉ s) : externalPiExtend ρ h x j = 0 := by
  simp [externalPiExtend_apply, hj]

/-- **Restriction after extension by zero is the identity.** -/
@[simp]
theorem restrict₂_externalPiExtend (h : s ⊆ t) (x : ∀ i : s, V i) :
    Finset.restrict₂ h (externalPiExtend ρ h x) = x :=
  funext fun i ↦ by simp

/-- Extending by zero from `s` to `t` and then to `u` is extending by zero from `s` to `u`. -/
@[simp]
theorem externalPiExtend_externalPiExtend (hst : s ⊆ t) (htu : t ⊆ u) (x : ∀ i : s, V i) :
    externalPiExtend ρ htu (externalPiExtend ρ hst x) = externalPiExtend ρ (hst.trans htu) x := by
  funext j
  by_cases hs : (j : ι) ∈ s
  · simp [hs, hst hs]
  · by_cases ht : (j : ι) ∈ t <;> simp [hs, ht]

/-- **The splitting over a disjoint union.** For disjoint `s` and `t`, the restrictions to `s` and
to `t` identify the product over `s ∪ t` with the product of the products over `s` and over `t`,
equivariantly for `(∀ i : s, G i) × (∀ i : t, G i) ≃* ∀ i : s ∪ t, G i`. -/
noncomputable def externalPiUnion (h : Disjoint s t) :
    Equiv ((externalPi fun i : (s ∪ t : Finset ι) ↦ ρ i).comp
        (MulEquiv.piFinsetUnion G h).toMonoidHom)
      (Representation.prod ((externalPi fun i : s ↦ ρ i).comp (MonoidHom.fst _ _))
        ((externalPi fun i : t ↦ ρ i).comp (MonoidHom.snd _ _))) :=
  .mk (LinearEquiv.piFinsetUnion k V h).symm fun g ↦ LinearMap.ext fun x ↦ by
    ext i
    · simp [Equiv.piFinsetUnion_left G h i.property]
    · simp [Equiv.piFinsetUnion_right G h i.property]

/-- The splitting over a disjoint union takes the restrictions to the two pieces. -/
@[simp]
theorem externalPiUnion_apply (h : Disjoint s t) (x : ∀ i : (s ∪ t : Finset ι), V i) :
    externalPiUnion ρ h x =
      (Finset.restrict₂ Finset.subset_union_left x,
        Finset.restrict₂ Finset.subset_union_right x) := by
  rw [externalPiUnion, Equiv.mk_apply]
  simp

/-- The inverse of the splitting over a disjoint union glues the two families. -/
@[simp]
theorem externalPiUnion_symm_apply (h : Disjoint s t) (x : (∀ i : s, V i) × ∀ i : t, V i) :
    (externalPiUnion ρ h).symm x = Equiv.piFinsetUnion V h x := by
  rw [externalPiUnion, Equiv.mk_symm, Equiv.mk_apply]
  simp

/-- Under the splitting over a disjoint union, the inclusion of the first factor is the extension
by zero from `s`. -/
theorem externalPiUnion_symm_inl (h : Disjoint s t) (x : ∀ i : s, V i) :
    (externalPiUnion ρ h).symm (x, 0) = externalPiExtend ρ Finset.subset_union_left x := by
  rw [externalPiUnion_symm_apply]
  funext ⟨i, hi⟩
  by_cases hs : i ∈ s
  · simp [Equiv.piFinsetUnion_left V h hs, hs]
  · simp [Equiv.piFinsetUnion_right V h ((Finset.mem_union.1 hi).resolve_left hs), hs]

/-- Under the splitting over a disjoint union, the inclusion of the second factor is the extension
by zero from `t`. -/
theorem externalPiUnion_symm_inr (h : Disjoint s t) (y : ∀ i : t, V i) :
    (externalPiUnion ρ h).symm (0, y) = externalPiExtend ρ Finset.subset_union_right y := by
  rw [externalPiUnion_symm_apply]
  funext ⟨i, hi⟩
  by_cases ht : i ∈ t
  · simp [Equiv.piFinsetUnion_right V h ht, ht]
  · simp [Equiv.piFinsetUnion_left V h ((Finset.mem_union.1 hi).resolve_right ht), ht]

end Finset

/-! ### Relabelling the index type -/

section CongrLeft

variable {ι' ι'' : Type*}

/-- **Relabelling the index type** along `e : ι' ≃ ι`: reading the coordinates through `e`
identifies the external product of `ρ` with that of the relabelled family `fun i' ↦ ρ (e i')`,
equivariantly for the relabelling `(∀ i', G (e i')) ≃* ∀ i, G i` of the groups. -/
noncomputable def externalPiCongrLeft (e : ι' ≃ ι) :
    Equiv ((externalPi ρ).comp (MulEquiv.piCongrLeft G e).toMonoidHom)
      (externalPi fun i' ↦ ρ (e i')) :=
  .mk (LinearEquiv.piCongrLeft k V e).symm fun g ↦ LinearMap.ext fun x ↦ funext fun i' ↦ by
    simp

/-- `externalPiCongrLeft ρ e` reads the coordinate at `i'` from `e i'`. -/
@[simp]
theorem externalPiCongrLeft_apply (e : ι' ≃ ι) (x : ∀ i, V i) (i' : ι') :
    externalPiCongrLeft ρ e x i' = x (e i') := by
  rw [externalPiCongrLeft, Equiv.mk_apply, LinearEquiv.piCongrLeft_symm_apply]

/-- The inverse of `externalPiCongrLeft ρ e` relabels the coordinates along `e`. -/
@[simp]
theorem externalPiCongrLeft_symm_apply (e : ι' ≃ ι) (x : ∀ i', V (e i')) :
    (externalPiCongrLeft ρ e).symm x = LinearEquiv.piCongrLeft k V e x := by
  rw [externalPiCongrLeft, Equiv.mk_symm, Equiv.mk_apply, LinearEquiv.symm_symm]

/-- **Relabelling is compatible with composition**: relabelling along `e₂` and then along `e₁` is
relabelling along `e₁.trans e₂`, on the underlying linear equivalences. -/
theorem externalPiCongrLeft_trans (e₁ : ι'' ≃ ι') (e₂ : ι' ≃ ι) :
    (externalPiCongrLeft ρ e₂).toLinearEquiv.trans
        (externalPiCongrLeft (fun i' ↦ ρ (e₂ i')) e₁).toLinearEquiv =
      (externalPiCongrLeft ρ (e₁.trans e₂)).toLinearEquiv := by
  simp only [externalPiCongrLeft, Equiv.toLinearEquiv_mk']
  rw [← LinearEquiv.trans_symm]
  exact congr_arg LinearEquiv.symm (LinearEquiv.piCongrLeft_trans k V e₁ e₂)

end CongrLeft

end Representation
