/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.HeckeOperator
public import TauCeti.RepresentationTheory.Smooth.Averaging
import TauCeti.Algebra.Module.NatInt
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic

/-!
# The operators `U_t = e_C ∘ ρ(t)` at a compact subgroup

Let `ρ` be a smooth representation of a group `G` on a module `V` over a commutative ring `A`,
where `G` carries a topology for which multiplication is separately continuous, and let `C` be a
compact subgroup of `G` whose pro-order is invertible in `A`, so that the averaging projector
`e_C` onto the invariants `V^C` is defined (`Representation.smoothAverage`). For `t ∈ G` the
operator `U_t = e_C ∘ ρ(t)` (`Representation.uOperator`) maps `V` into `V^C`. On `V^C` it depends
only on the double coset `C t C`, and it is `ρ(t)` when `t⁻¹ C t ⊆ C`. When `C ∩ t C t⁻¹` is open
in `C` (for instance when `C` is open), `U_t` is the average of the translates `ρ(q t)` over
representatives `q` of `C ⧸ (C ∩ t C t⁻¹)`. The double coset operator `[C t C]` is their sum
(`Representation.doubleCosetOperator_apply_eq_finsum`), and so
`[C t C] = [C : C ∩ t C t⁻¹] • U_t` on `V^C`, the index being the number of cosets `h C` in
`C t C`.

The operators `U_t` are not multiplicative in general. They are when `C` splits along `t` and `t'`:
if every `c ∈ C` factors as `c = a * b` with `t a t⁻¹ ∈ C` and `t'⁻¹ b t' ∈ C`, then
`U_t ∘ U_{t'} = U_{t t'}` on `V^C` (`Representation.uOperator_uOperator_apply`). The reason is
that averaging `ρ(t') v` over `C` is averaging it over the elements `a` alone, since the `b` fix
`ρ(t') v`, and `ρ(t)` conjugates these `a` into `C`
(`Representation.smoothAverage_apply_smoothAverage_of_forall_exists`). For the pro-`p` Iwahori
subgroup `C = I₁` of `GL_N` over a nonarchimedean local field and dominant diagonal `t`, `t'`, the
Iwahori factorisation of `I₁` into upper and lower triangular factors gives such splittings, and
`t ↦ U_t` is then a homomorphism from the dominant diagonal monoid to the endomorphisms of
`V^{I₁}`; `Representation.uOperatorHom` packages this for any submonoid all of whose pairs split
`C`.

## Main definitions

* `Representation.uOperator ρ C hC t`: the operator `U_t = e_C ∘ ρ(t)` on `V`.
* `Representation.invariantsUOperator ρ C hC t`: its restriction to `V^C`.
* `Representation.uOperatorHom ρ C hC T hT`: `t ↦ U_t` as a monoid homomorphism from a submonoid
  `T` of `G` to the endomorphisms of `V^C`, when every pair of elements of `T` splits `C`.

## Main results

* `Representation.smoothAverage_apply_smoothAverage_of_forall_exists`:
  `e_C (ρ(t) (e_C y)) = e_C (ρ(t) y)` when every `c ∈ C` is `a * b` with `t a t⁻¹ ∈ C` and `b`
  fixing `y`.
* `Representation.uOperator_uOperator_apply`: `U_t (U_{t'} v) = U_{t t'} v` for `v ∈ V^C`, when
  `C` splits along `t` and `t'`.
* `Representation.uOperator_mul_mul_apply_of_mem`, `Representation.uOperator_apply_of_forall_mem`:
  on `V^C`, `U_t` depends only on `C t C`, and `U_t v = ρ(t) v` when `t⁻¹ C t ⊆ C`.
* `Representation.uOperator_apply_eq_inverse_relIndex_smul_finsum`: for `C ∩ t C t⁻¹` open in
  `C`, `U_t` on `V^C` as the average of the translates `ρ(q t)`, `q ∈ C ⧸ (C ∩ t C t⁻¹)`.
* `Representation.doubleCosetOperator_apply_eq_relIndex_smul_uOperator`: for `C ∩ t C t⁻¹` open
  in `C`, `[C t C] = [C : C ∩ t C t⁻¹] • U_t` on `V^C`.

## References

* W. Casselman, *Introduction to the theory of admissible representations of `p`-adic reductive
  groups* (unpublished notes, 1995).
* T. J. Haines, R. E. Kottwitz and A. Prasad, *Iwahori–Hecke algebras*, J. Ramanujan Math. Soc.
  25 (2010), §1.

The formal proof of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC) proves the cases of the pro-`p` Iwahori subgroup of `GL_N` in
`src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` (`New.compactMean_diagGL_compactMean_diagGL`,
`New.iwahoriHeckeHom`) and `src/Lib/LocalGL/Iwahori/HeckeDegrees.lean`
(`New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`); the general statements here, for any
compact subgroup and any splitting, were written independently of its code.
-/

public section

namespace Representation

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V] (ρ : Representation A G V) [IsSmooth ρ]
  (C : Subgroup G) [CompactSpace C] (hC : TauCeti.HasUnitProOrder A C)

/-! ### Averages of translates -/

/-- Right translation by an element `a` with `t a t⁻¹ ∈ C` does not change the average over `C` of
a translate by `t`: `e_C (ρ(t a) y) = e_C (ρ(t) y)`. -/
theorem smoothAverage_apply_mul_of_mul_mul_inv_mem {t a : G} (ha : t * a * t⁻¹ ∈ C) (y : V) :
    smoothAverage (ρ.comp C.subtype) hC (ρ (t * a) y) =
      smoothAverage (ρ.comp C.subtype) hC (ρ t y) := by
  -- `ρ(t a) y = ρ(t a t⁻¹) (ρ(t) y)`, and `e_C` does not see the action of `t a t⁻¹ ∈ C`.
  have h : ρ (t * a) y = (ρ.comp C.subtype) ⟨t * a * t⁻¹, ha⟩ (ρ t y) := by
    simp [← mul_apply_eq_comp, ← map_mul]
  rw [h, smoothAverage_apply_apply]

/-- **Averaging before a translation.** If every `c ∈ C` factors as `c = a * b` with `t a t⁻¹ ∈ C`
and `ρ(b) y = y`, then averaging `y` over `C` before translating by `t` does not change the average
over `C`: `e_C (ρ(t) (e_C y)) = e_C (ρ(t) y)`. -/
theorem smoothAverage_apply_smoothAverage_of_forall_exists {t : G} {y : V}
    (h : ∀ c ∈ C, ∃ a b : G, c = a * b ∧ t * a * t⁻¹ ∈ C ∧ ρ b y = y) :
    smoothAverage (ρ.comp C.subtype) hC (ρ t (smoothAverage (ρ.comp C.subtype) hC y)) =
      smoothAverage (ρ.comp C.subtype) hC (ρ t y) := by
  -- Average `y` over the cosets of its stabilizer `H` in `C`; each translate `ρ(c) y` is
  -- `ρ(a) y` with `t a t⁻¹ ∈ C`, so each term contributes `e_C (ρ(t) y)`.
  set σ := ρ.comp C.subtype
  have hH := IsSmooth.isOpen_stabilizer (ρ := σ) y
  have : Finite (C ⧸ stabilizer σ y) := (stabilizer σ y).quotient_finite_of_isOpen hH
  have : Fintype (C ⧸ stabilizer σ y) := Fintype.ofFinite _
  have h_term (q : C ⧸ stabilizer σ y) :
      smoothAverage σ hC (ρ t (σ q.out y)) = smoothAverage σ hC (ρ t y) := by
    obtain ⟨a, b, hc, ha, hb⟩ := h q.out q.out.property
    -- `σ q.out y = ρ(a) (ρ(b) y) = ρ(a) y`
    have : σ q.out y = ρ a y := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hc, map_mul, mul_apply_eq_comp, hb]
    rw [this, ← smoothAverage_apply_mul_of_mul_mul_inv_mem ρ C hC ha y, map_mul,
      mul_apply_eq_comp]
  -- the `[C : H]` terms of the average each contribute `e_C (ρ(t) y)`
  have hsum : smoothAverage σ hC (ρ t (∑ᶠ q : C ⧸ stabilizer σ y, σ q.out y)) =
      (stabilizer σ y).index • smoothAverage σ hC (ρ t y) := by
    simp only [finsum_eq_sum_of_fintype, map_sum, h_term, Finset.sum_const, Finset.card_univ,
      Subgroup.index, Nat.card_eq_fintype_card]
  -- and `[C : H]` is invertible in `A`
  rw [smoothAverage_apply_of_le σ hC hH le_rfl, map_smul, map_smul, hsum,
    Ring.inverse_natCast_smul_nsmul (hC.isUnit_index hH)]

/-! ### The operators `U_t` -/

/-- **The operator `U_t = e_C ∘ ρ(t)`**: translate by `t`, then average over the compact subgroup
`C`. It maps `V` into the invariants `V^C` (`Representation.uOperator_apply_mem_invariants`). -/
noncomputable def uOperator (t : G) : V →ₗ[A] V :=
  smoothAverage (ρ.comp C.subtype) hC ∘ₗ ρ t

/-- The defining formula `U_t v = e_C (ρ(t) v)`. -/
theorem uOperator_apply (t : G) (v : V) :
    ρ.uOperator C hC t v = smoothAverage (ρ.comp C.subtype) hC (ρ t v) :=
  (rfl)

/-- The operator `U_t` takes values in the invariants `V^C`. -/
theorem uOperator_apply_mem_invariants (t : G) (v : V) :
    ρ.uOperator C hC t v ∈ invariants (ρ.comp C.subtype) :=
  smoothAverage_apply_mem_invariants _ hC _

/-- `U_t` does not change when `t` is multiplied on the left by an element of `C`. -/
theorem uOperator_mul_left_of_mem {c : G} (hc : c ∈ C) (t : G) :
    ρ.uOperator C hC (c * t) = ρ.uOperator C hC t := by
  ext v
  -- `ρ(c t) v = ρ(c) (ρ(t) v)` with `c ∈ C`, which `e_C` does not see.
  have h : ρ (c * t) v = (ρ.comp C.subtype) ⟨c, hc⟩ (ρ t v) := by
    simp [← mul_apply_eq_comp, ← map_mul]
  rw [uOperator_apply, uOperator_apply, h, smoothAverage_apply_apply]

/-- On `V^C`, `U_t` does not change when `t` is multiplied on the right by an element of `C`. -/
theorem uOperator_mul_right_apply_of_mem {c : G} (hc : c ∈ C) (t : G) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.uOperator C hC (t * c) v = ρ.uOperator C hC t v := by
  rw [uOperator_apply, uOperator_apply, map_mul, mul_apply_eq_comp]
  congr 2
  simpa using (mem_invariants _ v).1 hv ⟨c, hc⟩

/-- On `V^C`, `U_t` depends only on the double coset `C t C`. -/
theorem uOperator_mul_mul_apply_of_mem {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) (t : G) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.uOperator C hC (c * t * c') v = ρ.uOperator C hC t v := by
  rw [uOperator_mul_right_apply_of_mem ρ C hC hc' _ hv, uOperator_mul_left_of_mem ρ C hC hc]

/-- If `t⁻¹ C t ⊆ C` (for instance if `t` normalises `C`), then `U_t` is `ρ(t)` on `V^C`: the
average can be dropped. -/
theorem uOperator_apply_of_forall_mem {t : G} (ht : ∀ c ∈ C, t⁻¹ * c * t ∈ C) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) : ρ.uOperator C hC t v = ρ t v := by
  have hle : C ≤ C.map (MulAut.conj t) := fun c hc ↦
    Subgroup.mem_map.2 ⟨t⁻¹ * c * t, ht c hc, by simp [mul_assoc]⟩
  have hmem : ρ t v ∈ invariants (ρ.comp (C.map (MulAut.conj t)).subtype) := by
    rw [← ρ.map_invariants_comp_subtype t C]
    exact Submodule.mem_map_of_mem hv
  exact smoothAverage_apply_of_mem_invariants _ hC (invariants_comp_subtype_antitone hle hmem)

/-- On `V^C`, `U_c` is the identity for every `c ∈ C`. -/
theorem uOperator_apply_of_mem {c : G} (hc : c ∈ C) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) : ρ.uOperator C hC c v = v := by
  rw [uOperator_apply_of_forall_mem ρ C hC (fun c' hc' ↦ by
    exact C.mul_mem (C.mul_mem (C.inv_mem hc) hc') hc) hv]
  simpa using (mem_invariants _ v).1 hv ⟨c, hc⟩

/-- On `V^C`, `U_1` is the identity. -/
theorem uOperator_one_apply {v : V} (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.uOperator C hC 1 v = v :=
  uOperator_apply_of_mem ρ C hC C.one_mem hv

/-- **Multiplicativity of the operators `U_t`.** Suppose that every `c ∈ C` factors as `c = a * b`
with `t a t⁻¹ ∈ C` and `t'⁻¹ b t' ∈ C`. Then `U_t (U_{t'} v) = U_{t t'} v` for every
`v ∈ V^C`. -/
theorem uOperator_uOperator_apply {t t' : G}
    (h : ∀ c ∈ C, ∃ a b : G, c = a * b ∧ t * a * t⁻¹ ∈ C ∧ t'⁻¹ * b * t' ∈ C) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.uOperator C hC t (ρ.uOperator C hC t' v) = ρ.uOperator C hC (t * t') v := by
  rw [uOperator_apply, uOperator_apply, uOperator_apply,
    smoothAverage_apply_smoothAverage_of_forall_exists ρ C hC fun c hc ↦ ?_, map_mul,
    mul_apply_eq_comp]
  -- `b` fixes `ρ(t') v`, since `t'⁻¹ b t' ∈ C` and `v ∈ V^C`
  obtain ⟨a, b, hcab, ha, hb⟩ := h c hc
  refine ⟨a, b, hcab, ha, mem_stabilizer.1 ?_⟩
  rw [stabilizer_conj]
  exact Subgroup.mem_map.2 ⟨t'⁻¹ * b * t', mem_invariants_comp_subtype_iff.1 hv hb,
    by simp [mul_assoc]⟩

/-! ### The operators `U_t` on the invariants -/

/-- The operator `U_t` restricted to the invariants `V^C`. -/
noncomputable def invariantsUOperator (t : G) : Module.End A (invariants (ρ.comp C.subtype)) :=
  (ρ.uOperator C hC t).restrict fun v _ ↦ ρ.uOperator_apply_mem_invariants C hC t v

@[simp]
theorem coe_invariantsUOperator_apply (t : G) (v : invariants (ρ.comp C.subtype)) :
    (ρ.invariantsUOperator C hC t v : V) = ρ.uOperator C hC t v :=
  (rfl)

/-- On `V^C`, `U_1` is the identity. -/
@[simp]
theorem invariantsUOperator_one : ρ.invariantsUOperator C hC 1 = 1 := by
  ext v
  exact ρ.uOperator_one_apply C hC v.property

/-- **The operators `U_t` as a monoid homomorphism.** For a submonoid `T` of `G` such that every
pair `t, t' ∈ T` splits `C` (every `c ∈ C` is `a * b` with `t a t⁻¹ ∈ C` and
`t'⁻¹ b t' ∈ C`), `t ↦ U_t` is a monoid homomorphism from `T` to the endomorphisms of `V^C`. -/
noncomputable def uOperatorHom (T : Submonoid G)
    (hT : ∀ t ∈ T, ∀ t' ∈ T, ∀ c ∈ C,
      ∃ a b : G, c = a * b ∧ t * a * t⁻¹ ∈ C ∧ t'⁻¹ * b * t' ∈ C) :
    T →* Module.End A (invariants (ρ.comp C.subtype)) where
  toFun t := ρ.invariantsUOperator C hC t
  map_one' := ρ.invariantsUOperator_one C hC
  map_mul' t t' := by
    ext v
    exact (ρ.uOperator_uOperator_apply C hC (hT t t.property t' t'.property) v.property).symm

@[simp]
theorem uOperatorHom_apply (T : Submonoid G)
    (hT : ∀ t ∈ T, ∀ t' ∈ T, ∀ c ∈ C,
      ∃ a b : G, c = a * b ∧ t * a * t⁻¹ ∈ C ∧ t'⁻¹ * b * t' ∈ C) (t : T) :
    ρ.uOperatorHom C hC T hT t = ρ.invariantsUOperator C hC t :=
  (rfl)

/-! ### The double coset operator -/

section DoubleCoset

open Pointwise

/-- On `V^C`, the operator `U_t` is the average of the translates `ρ(q t) v` over representatives
`q` of `C ⧸ (C ∩ t C t⁻¹)`, when `C ∩ t C t⁻¹` is open in `C` (for instance when `C` is open,
by `Subgroup.isOpen_conjAct_smul_subgroupOf`). -/
theorem uOperator_apply_eq_inverse_relIndex_smul_finsum {t : G}
    (hopen : IsOpen (((ConjAct.toConjAct t • C).subgroupOf C : Subgroup C) : Set C)) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.uOperator C hC t v = Ring.inverse ((ConjAct.toConjAct t • C).relIndex C : A) •
      ∑ᶠ q : C ⧸ (ConjAct.toConjAct t • C).subgroupOf C, ρ ((q.out : G) * t) v := by
  -- `C ∩ t C t⁻¹` fixes `ρ(t) v`, since `t⁻¹ c t ∈ C` for its elements `c`.
  have hstab : (ConjAct.toConjAct t • C).subgroupOf C ≤ stabilizer (ρ.comp C.subtype) (ρ t v) :=
    fun c hc ↦ by
      rw [mem_stabilizer, MonoidHom.comp_apply, Subgroup.coe_subtype]
      apply mem_stabilizer.1
      rw [stabilizer_conj]
      exact Subgroup.mem_map.2 ⟨t⁻¹ * c * t, mem_invariants_comp_subtype_iff.1 hv
        (Subgroup.mem_conjAct_smul_iff.1 (Subgroup.mem_subgroupOf.1 hc)),
        by simp [mul_assoc]⟩
  rw [uOperator_apply, smoothAverage_apply_of_le _ hC hopen hstab, Subgroup.relIndex]
  simp [← mul_apply_eq_comp, ← map_mul]

/-- **The double coset operator and `U_t`.** For a compact subgroup `C` with `C ∩ t C t⁻¹` open in
`C` (for instance `C` compact open, by `Subgroup.isOpen_conjAct_smul_subgroupOf`) and `v ∈ V^C`,
the double coset operator `[C t C] v = ∑_{h C ⊆ C t C} ρ(h) v` is `[C : C ∩ t C t⁻¹]` times
`U_t v`; the index is the number of cosets `h C` in `C t C`. -/
theorem doubleCosetOperator_apply_eq_relIndex_smul_uOperator {t : G}
    (hopen : IsOpen (((ConjAct.toConjAct t • C).subgroupOf C : Subgroup C) : Set C)) {v : V}
    (hv : v ∈ invariants (ρ.comp C.subtype)) :
    ρ.doubleCosetOperator C t v = (ConjAct.toConjAct t • C).relIndex C • ρ.uOperator C hC t v := by
  have hu : IsUnit ((ConjAct.toConjAct t • C).relIndex C : A) := hC.isUnit_index hopen
  have : Finite (C ⧸ (ConjAct.toConjAct t • C).subgroupOf C) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have : ((ConjAct.toConjAct t • C).subgroupOf C).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  rw [uOperator_apply_eq_inverse_relIndex_smul_finsum ρ C hC hopen hv, smul_comm,
    Ring.inverse_natCast_smul_nsmul hu,
    doubleCosetOperator_apply_eq_finsum t (by rwa [weightSpace_one])]

end DoubleCoset

end Representation
