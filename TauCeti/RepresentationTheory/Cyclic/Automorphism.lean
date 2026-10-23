/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Data.ZMod.MonoidHomEquiv
import Mathlib.Tactic.Abel

/-!
# The cyclic representation of an automorphism of finite order

Let `T` be an additive commutative group, `m > 0`, and `A : T ≃+ T` an additive automorphism of
order dividing `m`, that is `A^[m] = id`. Then the cyclic group `C_m = Multiplicative (ZMod m)`
acts on `T` with its standard generator `ofAdd 1` acting by `A`; this is the integral
representation `AddEquiv.cyclicRep A hA : Rep ℤ C_m`. Its norm `N = ∑ g, ρ g` is the ordered sum
of powers `∑ j < m, A^j` (`AddEquiv.cyclicRepresentation_norm_apply`).

Its group cohomology is read off in
`TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicAutomorphism`.

## Main definitions

* `AddEquiv.cyclicRepresentation A hA`: the representation of `C_m` on `T` in which the
  generator acts by `A`.
* `AddEquiv.cyclicRep A hA`: the same representation, as an object of `Rep ℤ C_m`.
* `AddMonoidHom.cyclicRepHom f hA hB hf`: an additive map `f` with `f ∘ A = B ∘ f`, as a morphism
  of cyclic representations; it is compatible with composition
  (`AddMonoidHom.cyclicRepHom_comp`).

## Main results

* `AddEquiv.cyclicRepresentation_ofAdd_apply`: the element `a` of `C_m` acts by `A^[a.val]`.
* `AddEquiv.cyclicRepresentation_norm_apply`: the norm is the ordered sum of powers of `A`.
* `AddEquiv.mem_ker_cyclicRep_norm_iff`, `AddEquiv.mem_range_cyclicRep_norm_iff`: the kernel and
  image of the norm, in terms of the ordered sum of powers of `A`.
* `AddEquiv.mem_ker_cyclicRep_applyAsHom_sub_iff`,
  `AddEquiv.mem_range_cyclicRep_applyAsHom_sub_iff`: the kernel of `ρ(g) - 𝟙` for the generator
  `g` is the fixed points of `A`, and its image is that of `1 - A`.
* `AddEquiv.mem_ker_cyclicRep_refl_norm_iff`, `AddEquiv.mem_range_cyclicRep_refl_norm_iff`: for
  the trivial action, given by the identity automorphism, the kernel of the norm is the
  `m`-torsion and its image is `m T`.
* `AddMonoidHom.exists_apply_eq_sum_range_iterate`,
  `AddMonoidHom.sum_range_iterate_add_apply`: for an exact sequence `0 → Λ → E → T` with maps
  intertwining automorphisms of order dividing `m`, the norm of a lift of a norm-zero element of
  `T` is the image of a fixed point, and changing the lift by `l` adds the norm of `l`.
-/

public section

namespace AddEquiv

variable {T : Type*} [AddCommGroup T] {m : ℕ} [NeZero m] (A : T ≃+ T) (hA : (⇑A)^[m] = id)

/-- The integral representation of the cyclic group `C_m = Multiplicative (ZMod m)` on `T` in
which the generator `ofAdd 1` acts by an additive automorphism `A` of order dividing `m`. -/
noncomputable def cyclicRepresentation : Representation ℤ (Multiplicative (ZMod m)) T :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((TauCeti.zmodMonoidHomEquiv m (T ≃ₗ[ℤ] T)).symm ⟨A.toIntLinearEquiv, by
      ext x
      rw [LinearEquiv.coe_pow]
      simpa using congrFun hA x⟩)

/-- The element `a` of `C_m` acts on `T` by the `a.val`-th iterate of `A`. -/
theorem cyclicRepresentation_ofAdd_apply (a : ZMod m) (x : T) :
    A.cyclicRepresentation hA (.ofAdd a) x = (⇑A)^[a.val] x := by
  simp [cyclicRepresentation, LinearEquiv.coe_pow]

/-- The generator `ofAdd 1` of `C_m` acts on `T` by `A`. -/
@[simp]
theorem cyclicRepresentation_ofAdd_one_apply (x : T) :
    A.cyclicRepresentation hA (.ofAdd 1) x = A x := by
  rw [cyclicRepresentation_ofAdd_apply, ZMod.val_one_eq_one_mod]
  obtain rfl | hm := eq_or_ne m 1
  · simpa using (congrFun hA x).symm
  · rw [Nat.one_mod_eq_one.mpr hm, Function.iterate_one]

/-- The norm of the cyclic representation of `A` is the ordered sum of the powers
`A^0, …, A^(m-1)`. -/
theorem cyclicRepresentation_norm_apply (x : T) :
    (A.cyclicRepresentation hA).norm x = ∑ j ∈ Finset.range m, (⇑A)^[j] x := by
  rw [Representation.norm, LinearMap.sum_apply]
  -- Reindex `C_m` by the representatives `0, …, m - 1` of `ZMod m`.
  refine Finset.sum_nbij' (fun g : Multiplicative (ZMod m) ↦ g.toAdd.val)
    (fun j : ℕ ↦ Multiplicative.ofAdd (j : ZMod m)) ?_ ?_ ?_ ?_ ?_
  all_goals simp +contextual [ZMod.val_lt, Nat.mod_eq_of_lt, cyclicRepresentation_ofAdd_apply]

/-- The cyclic representation of `A` as an object of `Rep ℤ C_m`. -/
noncomputable abbrev cyclicRep : Rep ℤ (Multiplicative (ZMod m)) :=
  Rep.of (A.cyclicRepresentation hA)

open CategoryTheory Rep

/-- An element of `T` lies in the kernel of the norm of the cyclic representation of `A` exactly
when the ordered sum of its images under the powers of `A` vanishes. -/
theorem mem_ker_cyclicRep_norm_iff (x : T) :
    x ∈ LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap ↔
      ∑ j ∈ Finset.range m, (⇑A)^[j] x = 0 := by
  rw [LinearMap.mem_ker, Representation.IntertwiningMap.coe_toLinearMap, Rep.norm_apply, Rep.of_ρ,
    cyclicRepresentation_norm_apply]

/-- An element of `T` lies in the image of the norm of the cyclic representation of `A` exactly
when it is the ordered sum of the images of some `y` under the powers of `A`. -/
theorem mem_range_cyclicRep_norm_iff (x : T) :
    x ∈ LinearMap.range (A.cyclicRep hA).norm.asHom.hom.toLinearMap ↔
      ∃ y, ∑ j ∈ Finset.range m, (⇑A)^[j] y = x := by
  refine LinearMap.mem_range.trans (exists_congr fun y ↦ ?_)
  rw [Representation.IntertwiningMap.coe_toLinearMap, Rep.norm_apply, Rep.of_ρ,
    cyclicRepresentation_norm_apply]

/-- The map `ρ(g) - 𝟙` of the periodic resolution, for the generator `g = ofAdd 1`, sends `y` to
`A y - y`. -/
private theorem cyclicRep_applyAsHom_sub_apply (y : T) :
    (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap y = A y - y := by
  rw [sub_hom, Representation.IntertwiningMap.coe_toLinearMap,
    Representation.IntertwiningMap.coe_sub, Pi.sub_apply, applyAsHom_apply]
  simp

/-- An element of `T` lies in the kernel of `ρ(g) - 𝟙`, for the generator `g = ofAdd 1`, exactly
when it is fixed by `A`. -/
theorem mem_ker_cyclicRep_applyAsHom_sub_iff (x : T) :
    x ∈ LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap ↔
      A x = x := by
  rw [LinearMap.mem_ker, cyclicRep_applyAsHom_sub_apply, sub_eq_zero]

/-- An element of `T` lies in the image of `ρ(g) - 𝟙`, for the generator `g = ofAdd 1`, exactly
when it has the form `b - A b`: the images of `A - 1` and `1 - A` agree. -/
theorem mem_range_cyclicRep_applyAsHom_sub_iff (x : T) :
    x ∈ LinearMap.range (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap ↔
      ∃ b, b - A b = x := by
  rw [LinearMap.mem_range]
  -- `A y - y = b - A b` for `b = -y`.
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨-y, ?_⟩, fun ⟨b, hb⟩ ↦ ⟨-b, ?_⟩⟩
  · rw [← hy, cyclicRep_applyAsHom_sub_apply, map_neg]
    abel
  · rw [cyclicRep_applyAsHom_sub_apply, ← hb, map_neg]
    abel

/-! ### The trivial action -/

/-- The identity automorphism has order dividing every `n`. Its cyclic representation is the
trivial action of `C_n` on `T`. -/
theorem iterate_refl (n : ℕ) : (⇑(AddEquiv.refl T))^[n] = id :=
  Function.iterate_id n

/-- For the trivial action, the kernel of the norm is the `m`-torsion. -/
theorem mem_ker_cyclicRep_refl_norm_iff (x : T) :
    x ∈ LinearMap.ker ((refl T).cyclicRep (iterate_refl m)).norm.asHom.hom.toLinearMap ↔
      x ∈ Submodule.torsionBy ℤ T m := by
  rw [mem_ker_cyclicRep_norm_iff, Submodule.mem_torsionBy_iff, natCast_zsmul]
  simp

/-- For the trivial action, the image of the norm is `m T`. -/
theorem mem_range_cyclicRep_refl_norm_iff (x : T) :
    x ∈ LinearMap.range ((refl T).cyclicRep (iterate_refl m)).norm.asHom.hom.toLinearMap ↔
      ∃ y, m • y = x := by
  rw [mem_range_cyclicRep_norm_iff]
  simp

/-- For the trivial action, every element is fixed by the generator. -/
theorem mem_ker_cyclicRep_refl_applyAsHom_sub (x : T) :
    x ∈ LinearMap.ker
      (applyAsHom ((refl T).cyclicRep (iterate_refl m)) (.ofAdd 1) - 𝟙 _).hom.toLinearMap :=
  (mem_ker_cyclicRep_applyAsHom_sub_iff _ _ x).2 (refl_apply x)

/-- For the trivial action, the image of `ρ(g) - 𝟙`, for the generator `g`, is zero. -/
theorem mem_range_cyclicRep_refl_applyAsHom_sub_iff (x : T) :
    x ∈ LinearMap.range
      (applyAsHom ((refl T).cyclicRep (iterate_refl m)) (.ofAdd 1) - 𝟙 _).hom.toLinearMap ↔
      x = 0 := by
  rw [mem_range_cyclicRep_applyAsHom_sub_iff]
  simp [eq_comm]

end AddEquiv

namespace AddMonoidHom

universe u

variable {T M : Type u} [AddCommGroup T] [AddCommGroup M] {m : ℕ} [NeZero m] {A : T ≃+ T}
  {B : M ≃+ M} (f : T →+ M) (hA : (⇑A)^[m] = _root_.id) (hB : (⇑B)^[m] = _root_.id)
  (hf : ∀ x, f (A x) = B (f x))

/-- An additive map `f : T →+ M` with `f ∘ A = B ∘ f` is a morphism from the cyclic
representation of `A` to that of `B`. -/
noncomputable def cyclicRepHom : A.cyclicRep hA ⟶ B.cyclicRep hB :=
  Rep.ofHom
    { toLinearMap := f.toIntLinearMap
      isIntertwining' := fun g ↦ LinearMap.ext fun x ↦ by
        rw [← ofAdd_toAdd g, LinearMap.comp_apply, LinearMap.comp_apply,
          AddEquiv.cyclicRepresentation_ofAdd_apply, AddEquiv.cyclicRepresentation_ofAdd_apply]
        exact Function.Semiconj.iterate_right hf _ x }

/-- The morphism of cyclic representations defined by `f` is `f` on underlying groups. The
coercion is stated on the intertwining maps of the underlying representations, rather than of the
`Rep` objects, which is the form `simp` meets in applications. -/
@[simp]
theorem coe_cyclicRepHom_hom :
    DFunLike.coe (F := (A.cyclicRepresentation hA).IntertwiningMap (B.cyclicRepresentation hB))
      (f.cyclicRepHom hA hB hf).hom = f := by
  ext x
  simp [cyclicRepHom]

open CategoryTheory in
/-- The morphism of cyclic representations defined by a composite `g ∘ f` is the composite of the
morphisms defined by `f` and `g`. -/
theorem cyclicRepHom_comp {N : Type u} [AddCommGroup N] {C : N ≃+ N} (g : M →+ N)
    (hC : (⇑C)^[m] = _root_.id) (hg : ∀ x, g (B x) = C (g x)) :
    (g.comp f).cyclicRepHom hA hC (fun x ↦ (congrArg g (hf x)).trans (hg (f x))) =
      f.cyclicRepHom hA hB hf ≫ g.cyclicRepHom hB hC hg := by
  ext x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.coe_comp,
    Function.comp_apply, Representation.IntertwiningMap.coe_toLinearMap, coe_cyclicRepHom_hom,
    coe_comp]

end AddMonoidHom

namespace AddMonoidHom

/-! ### Norms along an equivariant exact sequence -/

variable {Λ E T : Type*} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup T] {m : ℕ}
  {AΛ : Λ ≃+ Λ} {AE : E ≃+ E} {AT : T ≃+ T} (i : Λ →+ E) (p : E →+ T)

/-- Changing the lift `s` by the image of `l : Λ` changes the norm `∑ j < m, AE^j s` by the image
of the norm `∑ j < m, AΛ^j l`. -/
theorem sum_range_iterate_add_apply (hi : ∀ x, i (AΛ x) = AE (i x)) (s : E) (l : Λ) :
    ∑ j ∈ Finset.range m, (⇑AE)^[j] (s + i l) =
      ∑ j ∈ Finset.range m, (⇑AE)^[j] s + i (∑ j ∈ Finset.range m, (⇑AΛ)^[j] l) := by
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iterate_map_add, Function.Semiconj.iterate_right hi j l]

/-- The norm `∑ j < m, AE^j s` of a lift `s` of a norm-zero element of `T` is the image of a
fixed point of `AΛ`. -/
theorem exists_apply_eq_sum_range_iterate [NeZero m] (hE : (⇑AE)^[m] = _root_.id)
    (hi : ∀ x, i (AΛ x) = AE (i x)) (hp : ∀ x, p (AE x) = AT (p x)) (hinj : Function.Injective i)
    (hexact : Function.Exact i p) {s : E}
    (hs : ∑ j ∈ Finset.range m, (⇑AT)^[j] (p s) = 0) :
    ∃ v : Λ, AΛ v = v ∧ i v = ∑ j ∈ Finset.range m, (⇑AE)^[j] s := by
  obtain ⟨v, hv⟩ := (hexact _).1 <| by
    rw [map_sum, ← hs]
    exact Finset.sum_congr rfl fun j _ ↦ Function.Semiconj.iterate_right hp j s
  refine ⟨v, hinj ?_, hv⟩
  -- The norm is fixed by `AE`.
  have hN := (AE.cyclicRepresentation hE).self_norm_apply (.ofAdd 1) s
  rwa [AddEquiv.cyclicRepresentation_ofAdd_one_apply, AddEquiv.cyclicRepresentation_norm_apply,
    ← hv, ← hi] at hN

end AddMonoidHom
