/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Order.SupClosed
public import TauCeti.Algebra.Coalgebra.Subcomodule.Lattice
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Finite subcomodules

This file proves that, when the coalgebra is projective as a module over a commutative
semiring, every element of a right comodule is contained in a finitely generated
subcomodule. It also packages the order-theoretic consequences: finite subcomodules
form a nonempty directed family, finite subsets and finitely generated submodules
are contained in one finite subcomodule, and the supremum and literal union of the
finite subcomodules are the whole comodule. Over a field these become statements
about finite-dimensional subcomodules through the same generic API.

For the elementwise result, the carrier is the span of the finitely many coefficients
occurring when the element's coaction is expanded in coordinates of the coalgebra. These
coordinates come from a splitting of `Finsupp.linearCombination R id : (C →₀ R) → C`, which
exists exactly when `C` is projective; a basis of a free coalgebra is a special case. The
counit shows that the original element lies in this span, and coordinate slices of
coassociativity show that the span is stable under the coaction.

No flatness or noetherian hypothesis is needed.

## Main declarations

* `TauCeti.Subcomodule.exists_finite_subcomodule_mem`: every element belongs to a
  subcomodule whose underlying module is finite.
* `TauCeti.Subcomodule.directedOn_finiteSubcomodules`: finite subcomodules form a
  directed family.
* `TauCeti.Subcomodule.sSup_finiteSubcomodules_eq_top`: for a projective coefficient coalgebra,
  the finite subcomodules have supremum `⊤`.
* `TauCeti.Subcomodule.exists_finite_le_of_mem`: every element of a subcomodule belongs to a
  finite subcomodule contained in it.
* `TauCeti.Subcomodule.finite_of_isAtom`: for a projective coefficient coalgebra, simple
  subcomodules are finite.
* `TauCeti.Subcomodule.instIsAtomic`: over a field every nonzero subcomodule contains a simple
  subcomodule.

## References

The directed-union theorem sequence from `nonempty_finiteSubcomodules` through
`iUnion_finiteSubcomodules_eq_univ_of_exists_mem` is adapted from the corresponding
subcoalgebra development in `TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite`.

See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Subcomodule

section General

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- **Coassociativity, read off in coordinates.** If `coact m` is a finite sum of tensors whose
left factors lie in `N`, then the component of `coact m` selected by any functional on `C` has
coaction landing again in `N ⊗[R] C`.

The submodule is otherwise arbitrary: containing the left factors is the only property used. -/
private theorem coact_coactComponent_mem_range {m : M} {N : Submodule R M} {s : Finset C}
    {a : C → M} (hm : Comodule.coact (R := R) (C := C) (M := M) m = ∑ c ∈ s, a c ⊗ₜ[R] c)
    (ha : ∀ c ∈ s, a c ∈ N) (f : C →ₗ[R] R) :
    Comodule.coact (R := R) (C := C) (M := M) (Comodule.coactComponent f m) ∈
      LinearMap.range (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C)) := by
  rw [Comodule.coact_coactComponent, hm]
  simp only [map_sum, LinearMap.lTensor_tmul]
  exact Submodule.sum_mem _ fun c hc ↦
    ⟨(⟨a c, ha c hc⟩ : N) ⊗ₜ[R] (LinearMap.tensorComponent f ∘ₗ Coalgebra.comul) c, rfl⟩

/-- **The counit identity, read off in coordinates.** If `coact m` is a finite sum of tensors whose
left factors lie in `N`, then applying the counit shows that `m` lies in `N`. -/
private theorem mem_of_coact_eq_sum {m : M} {N : Submodule R M} {s : Finset C} {a : C → M}
    (hm : Comodule.coact (R := R) (C := C) (M := M) m = ∑ c ∈ s, a c ⊗ₜ[R] c)
    (ha : ∀ c ∈ s, a c ∈ N) : m ∈ N := by
  have hcounit := Comodule.lTensor_counit_coact (R := R) (C := C) (M := M) m
  rw [hm] at hcounit
  apply_fun TensorProduct.rid R M at hcounit
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, one_smul] at hcounit
  rw [← hcounit]
  exact Submodule.sum_mem N fun c hc ↦ N.smul_mem _ (ha c hc)

/-- If a coalgebra is projective as a module over a commutative semiring, every element
of a right comodule belongs to a subcomodule that is finitely generated as a
module. -/
theorem exists_finite_subcomodule_mem [Module.Projective R C] (m : M) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N := by
  classical
  -- Coordinates of `coact m` along a splitting `σ` of `Finsupp.linearCombination R id`.
  obtain ⟨σ, hσ⟩ := Module.projective_def'.mp ‹Module.Projective R C›
  let a : C →₀ M := TensorProduct.finsuppScalarRight R R M C
    (σ.lTensor M (Comodule.coact (R := R) (C := C) (M := M) m))
  have ha (c : C) : a c = Comodule.coactComponent ((Finsupp.lapply c).comp σ) m := by
    simp only [a, Comodule.coactComponent_apply, LinearMap.tensorComponent_def]
    generalize Comodule.coact (R := R) (C := C) (M := M) m = t
    induction t using TensorProduct.inductionOn with
    | tmul n d => simp
    | add x y hx hy => simp [hx, hy]
  have hrepr : Comodule.coact (R := R) (C := C) (M := M) m = ∑ c ∈ a.support, a c ⊗ₜ[R] c := by
    calc Comodule.coact (R := R) (C := C) (M := M) m =
          (Finsupp.linearCombination R id).lTensor M
            ((TensorProduct.finsuppScalarRight R R M C).symm a) := by
          simp [a, ← LinearMap.lTensor_comp_apply, hσ]
      _ = _ := by
          conv_lhs => rw [← a.sum_single]
          simp [Finsupp.sum, map_sum]
  let N := Submodule.span R (Set.range a)
  have ha_mem (c : C) : a c ∈ N :=
    Submodule.subset_span (Set.mem_range_self c)
  have hstable :
      ∀ n ∈ N,
        Comodule.coact (R := R) (C := C) (M := M) n ∈
          LinearMap.range
            (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C)) := by
    intro n hn
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hn
    · rintro _ ⟨c, rfl⟩
      rw [ha c]
      exact coact_coactComponent_mem_range hrepr (fun c _ ↦ ha_mem c) _
    · intro x y _ _ hx hy
      simpa only [map_add] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).add_mem hx hy
    · intro r x _ hx
      simpa only [map_smul] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).smul_mem r hx
  refine ⟨ofSubmodule (R := R) (C := C) (M := M) N hstable, ?_, ?_⟩
  · have hSN : (ofSubmodule (R := R) (C := C) (M := M) N hstable).toSubmodule = N := by
      rw [toSubmodule_carrier]
      exact ofSubmodule_carrier N hstable
    rw [hSN]
    exact Module.Finite.span_of_finite R a.finite_range
  · exact mem_ofSubmodule.mpr (mem_of_coact_eq_sum hrepr fun c _ ↦ ha_mem c)

/-- The set of subcomodules that are finitely generated as `R`-modules. -/
def finiteSubcomodules : Set (Subcomodule R C M) :=
  {N | Module.Finite R N.toSubmodule}

@[simp]
theorem mem_finiteSubcomodules {N : Subcomodule R C M} :
    N ∈ finiteSubcomodules (R := R) (C := C) (M := M) ↔
      Module.Finite R N.toSubmodule :=
  Iff.rfl

/-- The zero subcomodule makes the family of finite subcomodules nonempty. -/
theorem nonempty_finiteSubcomodules : (finiteSubcomodules (R := R) (C := C) (M := M)).Nonempty := by
  refine ⟨⊥, ?_⟩
  rw [mem_finiteSubcomodules]
  exact Module.Finite.bot R M

/-- Finite subcomodules are closed under binary joins. -/
theorem supClosed_finiteSubcomodules :
    SupClosed (finiteSubcomodules (R := R) (C := C) (M := M)) := by
  intro N hN P hP
  rw [mem_finiteSubcomodules] at hN hP ⊢
  let : Module.Finite R N.toSubmodule := hN
  let : Module.Finite R P.toSubmodule := hP
  exact sup_finite N P

/-- Finite subcomodules form a directed family under inclusion. -/
theorem directedOn_finiteSubcomodules :
    DirectedOn (· ≤ ·) (finiteSubcomodules (R := R) (C := C) (M := M)) :=
  supClosed_finiteSubcomodules.directedOn

/-- The carrier of the supremum of all finite subcomodules is their literal union. -/
@[simp]
theorem coe_sSup_finiteSubcomodules : ((sSup (finiteSubcomodules (R := R) (C := C) (M := M)) :
        Subcomodule R C M) : Set M) =
      ⋃ N : finiteSubcomodules (R := R) (C := C) (M := M), (N.1 : Set M) :=
  coe_sSup_of_directedOn nonempty_finiteSubcomodules directedOn_finiteSubcomodules

/-- Membership in the supremum of all finite subcomodules means membership in one finite
subcomodule. -/
@[simp]
theorem mem_sSup_finiteSubcomodules {m : M} :
    m ∈ sSup (finiteSubcomodules (R := R) (C := C) (M := M)) ↔
      ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N := by
  simpa only [mem_finiteSubcomodules] using
    (mem_sSup_of_directedOn nonempty_finiteSubcomodules directedOn_finiteSubcomodules (m := m))

/-- If every element lies in a finite subcomodule, then every finite set lies in one finite
subcomodule. -/
theorem exists_finite_subcomodule_of_setFinite_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    {s : Set M} (hs : s.Finite) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ s ⊆ N := by
  classical
  obtain ⟨N, hNfinite, hsN⟩ :=
    DirectedOn.exists_mem_subset_of_finset_subset_biUnion
      (f := fun N : Subcomodule R C M => (N : Set M))
      nonempty_finiteSubcomodules directedOn_finiteSubcomodules
      (s := hs.toFinset) (by
        intro m _
        obtain ⟨N, hNfinite, hmN⟩ := hM m
        exact Set.mem_iUnion₂_of_mem
          (mem_finiteSubcomodules.mpr hNfinite) hmN)
  exact ⟨N, mem_finiteSubcomodules.mp hNfinite, by
    simpa only [hs.coe_toFinset] using hsN⟩

/-- If every element lies in a finite subcomodule, then every finitely generated submodule lies
in one finite subcomodule. -/
theorem exists_finite_subcomodule_of_fg_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (P : Submodule R M) (hP : P.FG) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ P ≤ N.toSubmodule := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hP
  obtain ⟨N, hNfinite, hsN⟩ :=
    exists_finite_subcomodule_of_setFinite_of_exists_mem hM hs
  refine ⟨N, hNfinite, ?_⟩
  rw [← hspan]
  exact Submodule.span_le.2 hsN

/-- If every element lies in a finite subcomodule, then the supremum of all finite
subcomodules is the whole comodule. -/
theorem sSup_finiteSubcomodules_eq_top_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    sSup (finiteSubcomodules (R := R) (C := C) (M := M)) = ⊤ := by
  apply top_unique
  intro m _
  exact mem_sSup_finiteSubcomodules.2 (hM m)

/-- If every element lies in a finite subcomodule, then the union of all finite subcomodules is
the whole carrier. -/
theorem iUnion_finiteSubcomodules_eq_univ_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    (⋃ N : finiteSubcomodules (R := R) (C := C) (M := M), (N.1 : Set M)) =
      Set.univ := by
  rw [← coe_sSup_finiteSubcomodules, sSup_finiteSubcomodules_eq_top_of_exists_mem hM]
  rfl

/-- If the coefficient coalgebra is projective, every finite set lies in a finite subcomodule. -/
theorem exists_finite_subcomodule_of_setFinite [Module.Projective R C] {s : Set M} (hs : s.Finite) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ s ⊆ N :=
  exists_finite_subcomodule_of_setFinite_of_exists_mem exists_finite_subcomodule_mem hs

/-- If the coefficient coalgebra is projective, every finitely generated submodule lies in a finite
subcomodule. -/
theorem exists_finite_subcomodule_of_fg [Module.Projective R C] (P : Submodule R M) (hP : P.FG) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ P ≤ N.toSubmodule :=
  exists_finite_subcomodule_of_fg_of_exists_mem exists_finite_subcomodule_mem P hP

/-- If the coefficient coalgebra is projective, the finite subcomodules have supremum `⊤`. -/
@[simp]
theorem sSup_finiteSubcomodules_eq_top [Module.Projective R C] :
    sSup (finiteSubcomodules (R := R) (C := C) (M := M)) = ⊤ :=
  sSup_finiteSubcomodules_eq_top_of_exists_mem exists_finite_subcomodule_mem

/-- If the coefficient coalgebra is projective, the union of the finite subcomodules is the whole
carrier. -/
@[simp]
theorem iUnion_finiteSubcomodules_eq_univ [Module.Projective R C] :
    (⋃ (N : Subcomodule R C M) (_ : Module.Finite R N.toSubmodule), (N : Set M)) =
      Set.univ := by
  simpa only [Set.iUnion_coe_set, mem_finiteSubcomodules] using
    iUnion_finiteSubcomodules_eq_univ_of_exists_mem exists_finite_subcomodule_mem

/-- If the coefficient coalgebra is projective, every element of a subcomodule `Q` belongs to a
finite subcomodule contained in `Q`. -/
theorem exists_finite_le_of_mem [Module.Projective R C] {Q : Subcomodule R C M} {m : M}
    (hm : m ∈ Q) : ∃ N : Subcomodule R C M, N ≤ Q ∧ Module.Finite R N.toSubmodule ∧ m ∈ N := by
  -- Find a finite subcomodule of the comodule `Q` containing `m` and include it back into `M`.
  obtain ⟨N, hN, hmN⟩ := exists_finite_subcomodule_mem (R := R) (C := C) (⟨m, hm⟩ : Q)
  have : Module.Finite R N := hN
  exact ⟨N.map (subtype Q), map_le_iff.mpr fun n _ ↦ by simp, map_finite (subtype Q) N,
    by simpa using mem_map_of_mem (subtype Q) hmN⟩

/-- If the coefficient coalgebra is projective, a simple subcomodule is finite. -/
theorem finite_of_isAtom [Module.Projective R C] {S : Subcomodule R C M} (hS : IsAtom S) :
    Module.Finite R S := by
  obtain ⟨v, hvS, hv0⟩ := ne_bot_iff.mp hS.1
  obtain ⟨F, hFS, hF, hvF⟩ := exists_finite_le_of_mem hvS
  rw [← (hS.le_iff.mp hFS).resolve_left (ne_bot_iff.mpr ⟨v, hvF, hv0⟩)]
  exact hF

end General

section Field

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k C M]

/-- **Every nonzero subcomodule over a field contains a simple subcomodule.** -/
instance instIsAtomic : IsAtomic (Subcomodule k C M) := by
  -- A nonzero finite-dimensional subcomodule of minimal dimension inside `b` is simple.
  refine ⟨fun b ↦ or_iff_not_imp_left.mpr fun hb ↦ ?_⟩
  obtain ⟨v, hvb, hv0⟩ := ne_bot_iff.mp hb
  obtain ⟨F, hFb, hF, hvF⟩ := exists_finite_le_of_mem hvb
  obtain ⟨A, ⟨hAF, hA0⟩, hmin⟩ :=
    (measure fun A : Subcomodule k C M ↦ Module.finrank k A.toSubmodule).wf.has_min
      {A | A ≤ F ∧ A ≠ ⊥} ⟨F, le_rfl, ne_bot_iff.mpr ⟨v, hvF, hv0⟩⟩
  refine ⟨A, ⟨hA0, fun B hBA ↦ by_contra fun hB0 ↦ ?_⟩, hAF.trans hFb⟩
  have : Module.Finite k A.toSubmodule :=
    Submodule.finiteDimensional_of_le (toSubmodule_le_toSubmodule.mpr hAF)
  exact hmin B ⟨hBA.le.trans hAF, hB0⟩ (Submodule.finrank_lt_finrank_of_lt hBA)

end Field

end Subcomodule

end TauCeti
