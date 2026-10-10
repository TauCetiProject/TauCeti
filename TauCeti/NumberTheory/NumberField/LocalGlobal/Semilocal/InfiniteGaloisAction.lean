/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.DecompositionGroup

import Mathlib.Algebra.Group.Pi.Units

/-!
# The Galois action on the semi-local algebra at an infinite place

Let `L/K` be an extension of number fields and `v` an infinite place of `K`. An automorphism `σ`
of `L/K` acts on the semi-local algebra `K_v ⊗[K] L` through the second factor, by `id ⊗ σ`;
this is the base change `TauCeti.Algebra.TensorProduct.baseChangeAutHom` of `σ` to `K_v`. Under
the semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` it permutes the factors: the component
at `σ • w` of `(id ⊗ σ) z` is the component of `z` at `w`, transported along the isomorphism of
completions `L_w ≃ L_{σ • w}` induced by `σ` (`infiniteSemilocalEquiv_baseChangeAutHom`).

When `L/K` is Galois, the Galois group permutes the places above `v` transitively, and the
stabilizer of one place `w` — its decomposition group — acts on `L_w`. The units of the
semi-local algebra are then **coinduced** from the decomposition group: as integral
representations of `Gal(L/K)`,

```text
(K_v ⊗[K] L)ˣ ≅ Coind_{D_w}^{Gal(L/K)} L_wˣ,
```

the map sending `y` to the function `g ↦ ((id ⊗ g) y)_w` (`infiniteSemilocalUnitsCoindIso`);
as at the finite places, its bijectivity is an instance of
`TauCeti.resCoindToHom_bijective_of_transport`.
Shapiro's lemma therefore computes the cohomology of `∏_{w ∣ v} L_wˣ` from the Galois cohomology
of the archimedean local field `L_w`. This is the archimedean counterpart of
`TauCeti.semilocalUnitsCoindIso` at the finite places.

## Main definitions

* `TauCeti.GlobalNumberFields.infiniteSemilocalUnitsRep`: the units of `K_v ⊗[K] L`, as an
  integral representation of `Aut(L/K)`.
* `TauCeti.GlobalNumberFields.infiniteDecompositionUnitsRep`: the units of `L_w`, as an integral
  representation of the decomposition group of `w`.
* `TauCeti.GlobalNumberFields.infiniteSemilocalUnitsToCoind`: the map
  `y ↦ (g ↦ ((id ⊗ g) y)_w)` into the coinduced representation.
* `TauCeti.GlobalNumberFields.infiniteSemilocalUnitsCoindIso`: for `L/K` Galois, that map as an
  isomorphism of representations.

## Main results

* `TauCeti.GlobalNumberFields.infiniteSemilocalEquiv_baseChangeAutHom`: under the
  semi-local decomposition, `id ⊗ σ` carries the factor at `w` to the factor at `σ • w` by the
  isomorphism of completions.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 (the cohomology of `∏_{w ∣ v} L_wˣ`).
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3) and Chapter VI, §2.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace CategoryTheory
open scoped TensorProduct NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

section GaloisHom

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  {v : InfinitePlace K}

/-- **The Galois action permutes the semi-local factors.** If `σ` carries the place `w` above `v`
to `w'`, then the component at `w'` of `(id ⊗ σ) z` is the component of `z` at `w`, transported
along the isomorphism of completions `L_w ≃ L_{w'}` induced by `σ`. -/
theorem infiniteSemilocalEquiv_baseChangeAutHom (σ : L ≃ₐ[K] L)
    {w w' : {w : InfinitePlace L // w.LiesOver v}} (h : w'.1 = σ • w.1)
    (z : v.Completion ⊗[K] L) :
    infiniteSemilocalEquiv L v (Algebra.TensorProduct.baseChangeAutHom v.Completion L σ z) w' =
      completionCongr v σ h (infiniteSemilocalEquiv L v z w) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [Algebra.TensorProduct.baseChangeAutHom_tmul, infiniteSemilocalEquiv_tmul,
      infiniteSemilocalEquiv_tmul, map_mul, AlgEquiv.commutes, Completion.algebraMap_apply,
      Completion.algebraMap_apply, completionCongr_algebraMap]
  | add x y hx hy => simp [map_add, hx, hy]

end GaloisHom

section Coinduction

universe u

variable {K : Type u} [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
  [Algebra K L] (v : InfinitePlace K)

/-- The units of the semi-local algebra `K_v ⊗[K] L` at an infinite place `v`, as an integral
representation of `Aut(L/K)` acting through `Algebra.TensorProduct.baseChangeAutHom`. -/
abbrev infiniteSemilocalUnitsRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.res (Algebra.TensorProduct.baseChangeAutHom v.Completion L)
    (Rep.ofAlgebraAutOnUnits v.Completion (v.Completion ⊗[K] L))

variable {L} (w : InfinitePlace L) [w.LiesOver v]

/-- The units of the completion `L_w` at an infinite place, as an integral representation of the
decomposition group of `w` acting through `decompositionHom`. -/
abbrev infiniteDecompositionUnitsRep : Rep ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
  Rep.res (decompositionHom v w) (Rep.ofAlgebraAutOnUnits v.Completion w.Completion)

/-- The component at `w` of the semi-local units, an equivariant map for the decomposition
group of `w`. -/
private def infiniteSemilocalUnitsComponent :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (infiniteSemilocalUnitsRep L v) ⟶
      infiniteDecompositionUnitsRep v w :=
  Rep.ofHom ⟨(Units.map ((Pi.evalMonoidHom
      (fun w' : {w : InfinitePlace L // w.LiesOver v} ↦ w'.1.Completion) ⟨w, ‹_›⟩).comp
      (infiniteSemilocalEquiv L v : v.Completion ⊗[K] L →* _))).toAdditive.toIntLinearMap,
    fun d ↦ LinearMap.ext fun y : Additive (v.Completion ⊗[K] L)ˣ ↦
      Additive.toMul.injective <| Units.ext <|
        -- an element of the decomposition group fixes `w`, so it acts on the factor at `w`
        (infiniteSemilocalEquiv_baseChangeAutHom (w := ⟨w, ‹_›⟩) (w' := ⟨w, ‹_›⟩)
          (d : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp d.2).symm _).trans
            (DFunLike.congr_fun (decompositionHom_apply d) _).symm⟩

/-- The map `y ↦ (g ↦ ((id ⊗ g) y)_w)` from the semi-local units at an infinite place to the
representation coinduced from the units of `L_w`. It is the morphism adjoint to the projection to
the factor at `w`, which is equivariant for the decomposition group of `w`. -/
def infiniteSemilocalUnitsToCoind :
    infiniteSemilocalUnitsRep L v ⟶
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (infiniteDecompositionUnitsRep v w) :=
  Rep.resCoindToHom _ _ _ (infiniteSemilocalUnitsComponent v w)

/-- The value of `infiniteSemilocalUnitsToCoind` at `g` is the component at `w` of
`(id ⊗ g) y`. -/
theorem infiniteSemilocalUnitsToCoind_apply (y : (v.Completion ⊗[K] L)ˣ) (g : L ≃ₐ[K] L) :
    ((Additive.toMul (α := w.Completionˣ)
      (((infiniteSemilocalUnitsToCoind v w).hom (Additive.ofMul y)).1 g) : w.Completionˣ) :
        w.Completion) =
      infiniteSemilocalEquiv L v (Algebra.TensorProduct.baseChangeAutHom v.Completion L g y)
        ⟨w, ‹_›⟩ :=
  (rfl)

omit [NumberField K] [NumberField L] in
/-- For `L/K` Galois, every place above `v` is carried to `w` by some automorphism. -/
private theorem exists_eq_smul [IsGalois K L] (w' : {w' : InfinitePlace L // w'.LiesOver v}) :
    ∃ g : L ≃ₐ[K] L, w = g • w'.1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_comap_eq (k := K) (w := w'.1) (w' := w)
    (by rw [LiesOver.comap_eq w'.1 v, LiesOver.comap_eq w v])
  exact ⟨g, hg.symm⟩

omit [NumberField K] [NumberField L] in
/-- Every automorphism carries some place above `v` to `w`, namely the translate of `w` by its
inverse. -/
private theorem exists_place_eq_smul (g : L ≃ₐ[K] L) :
    ∃ w' : {w' : InfinitePlace L // w'.LiesOver v}, w = g • w'.1 :=
  ⟨⟨g⁻¹ • w, inferInstance⟩, (smul_inv_smul g w).symm⟩

/-- For `L/K` Galois, `infiniteSemilocalUnitsToCoind` is bijective: the semi-local units are the
product of the units of the completions above `v`, which `id ⊗ g` permutes through
`completionCongr`. -/
private theorem infiniteSemilocalUnitsToCoind_bijective [IsGalois K L] :
    Function.Bijective (infiniteSemilocalUnitsToCoind v w).hom :=
  resCoindToHom_bijective_of_transport (p := fun i : {w : InfinitePlace L // w.LiesOver v} ↦ i.1)
    (w := ⟨w, ‹_›⟩) (M := fun i ↦ i.1.Completionˣ)
    (T := fun g _ _ h ↦ (Units.mapEquiv (completionCongr v g h).toMulEquiv).toEquiv)
    (infiniteSemilocalUnitsComponent v w)
    (Additive.toMul.trans
      ((Units.mapEquiv (infiniteSemilocalEquiv L v).toMulEquiv).trans MulEquiv.piUnits).toEquiv)
    (fun g y _ _ h ↦ Units.ext (infiniteSemilocalEquiv_baseChangeAutHom g h
      (Additive.toMul (α := (v.Completion ⊗[K] L)ˣ) y).1)) Additive.toMul (fun _ ↦ rfl)
    (fun d a ↦ Units.ext (DFunLike.congr_fun (decompositionHom_apply (v := v) (w := w) d)
      (Additive.toMul (α := w.Completionˣ) a).1))
    (fun g g' _ _ _ h h' a ↦
      Units.ext (DFunLike.congr_fun (completionCongr_trans (v := v) g g' h h') a.1))
    (exists_eq_smul v w) (exists_place_eq_smul v w)

/-- **The semi-local units at an infinite place are coinduced.** For `L/K` Galois and `w` a
place above the infinite place `v`, the units of `K_v ⊗[K] L` are, as an integral representation
of `Gal(L/K)`, coinduced from the units of `L_w` as a representation of the decomposition group
of `w`. -/
def infiniteSemilocalUnitsCoindIso [IsGalois K L] :
    infiniteSemilocalUnitsRep L v ≅
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (infiniteDecompositionUnitsRep v w) :=
  Rep.mkIso ((infiniteSemilocalUnitsToCoind v w).hom.ofBijective
    (infiniteSemilocalUnitsToCoind_bijective v w))

/-- The coinduction isomorphism is `infiniteSemilocalUnitsToCoind`. -/
@[simp]
theorem infiniteSemilocalUnitsCoindIso_hom [IsGalois K L] :
    (infiniteSemilocalUnitsCoindIso v w).hom = infiniteSemilocalUnitsToCoind v w :=
  (rfl)

end Coinduction

end TauCeti.GlobalNumberFields
