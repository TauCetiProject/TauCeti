/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic
import TauCeti.GroupTheory.GroupAlgGeom.Linear
import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Proper quotients of coordinate groups of generalised equations

The coordinate group of a generalised equation `Ω'` over `F = F(A)` is a *proper quotient* of that
of `Ω` when there is a surjective, non-injective `F`-homomorphism `F_{R(Ω)} → F_{R(Ω')}`. There is
no infinite descending chain of proper quotients. The coordinate groups of such a chain are
quotients of the first one, which is generated over `F` by the finitely many items of its
generalised equation; they are separated by `F`, and `F` is equationally Noetherian, of any rank,
so the descending chain condition for separated groups applies. In particular no coordinate group
is a proper quotient of itself. This is what makes the Makanin–Razborov process stop: each branch
of its solution tree ends at a proper quotient, and the construction is repeated below it.

## Main definitions

* `TauCeti.GenEq.IsProperQuotient`: the coordinate group of `Ω'` is a proper quotient of that of
  `Ω`.

## Main results

* `TauCeti.GenEq.wellFounded_isProperQuotient`: there is no infinite descending chain of proper
  quotients of coordinate groups of generalised equations.
* `TauCeti.GenEq.isProperQuotient_irrefl`: no coordinate group is a proper quotient of itself.
* `TauCeti.GenEq.IsProperQuotient.trans`: a proper quotient of a proper quotient is a proper
  quotient.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.6 (finiteness of the solution tree).
* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §2, Lemma 3.
-/

public section

open TauCeti.GroupAlgGeom Monoid.Coprod

namespace TauCeti.GenEq

variable {A : Type*}

/-- The coordinate group of `Ω'` is a *proper quotient* of that of `Ω`: there is a surjective,
non-injective `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω')}`. -/
def IsProperQuotient (Ω' Ω : GenEq A) : Prop :=
  ∃ φ : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) Ω'.toSystem),
    Function.Surjective φ ∧ ¬ Function.Injective φ

/-- The coordinate group of `Ω'` is a proper quotient of that of `Ω` exactly when there is a
surjective, non-injective `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω')}`. -/
theorem isProperQuotient_iff {Ω' Ω : GenEq A} : IsProperQuotient Ω' Ω ↔
    ∃ φ : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) Ω'.toSystem),
      Function.Surjective φ ∧ ¬ Function.Injective φ := Iff.rfl

/-- There is no infinite descending chain of proper quotients of coordinate groups of generalised
equations over a free group `F(A)`, whatever the rank of `F(A)`. -/
theorem wellFounded_isProperQuotient : WellFounded (IsProperQuotient (A := A)) := by
  refine wellFounded_iff_isEmpty_descending_chain.2 ⟨fun ⟨Ω, hΩ⟩ ↦ ?_⟩
  choose φ hsurj hinj using hΩ
  -- The quotient map presents the first coordinate group on the finitely many items of `Ω 0`.
  let S := (Ω 0).toSystem
  let π := evalGHom (CoordGroup.coeff (.id (FreeGroup A)) S)
    (CoordGroup.genericPoint (.id (FreeGroup A)) S)
  have hπ : Function.Surjective π := fun q ↦ by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨w, by simp [π]⟩
  obtain ⟨m, hm⟩ := (isEquationallyNoetherian_freeGroup (.id _)).exists_forall_ge_injective π hπ
    φ hsurj fun _ ↦ CoordGroup.isSeparatedBy_coeff _
  exact hinj m (hm m le_rfl)

/-- No coordinate group of a generalised equation is a proper quotient of itself. -/
theorem isProperQuotient_irrefl (Ω : GenEq A) : ¬ IsProperQuotient Ω Ω :=
  wellFounded_isProperQuotient.irrefl.irrefl Ω

/-- A proper quotient of a proper quotient of the coordinate group of `Ω₃` is a proper quotient
of it. -/
theorem IsProperQuotient.trans {Ω₁ Ω₂ Ω₃ : GenEq A} (h₁₂ : IsProperQuotient Ω₁ Ω₂)
    (h₂₃ : IsProperQuotient Ω₂ Ω₃) : IsProperQuotient Ω₁ Ω₃ := by
  obtain ⟨φ, hφ, -⟩ := h₁₂
  obtain ⟨ψ, hψ, hψi⟩ := h₂₃
  exact ⟨φ.comp ψ, GHom.coe_comp φ ψ ▸ hφ.comp hψ, fun h ↦ hψi (GHom.coe_comp φ ψ ▸ h).of_comp⟩

/-! ### Example -/

/-- The generalised equation with one item `h₀`, no variable bases and the constant bases `C`. -/
private abbrev oneItem (C : Finset (Fin 1 × (A × Bool))) : GenEq A where
  numItems := 1
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right μ := μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive μ := μ.elim0
  constBases := C
  connections := ∅
  bounds_of_mem_connections _ hc := absurd hc (Finset.notMem_empty _)
  dual_mem_connections _ hc := absurd hc (Finset.notMem_empty _)

/-- The coordinate group of the generalised equation `h₀ = a` is a proper quotient of that of one
free item: the identity on `h₀` induces a surjection, which kills `h₀ a⁻¹`, an equation that does
not vanish at `h₀ = 1`. -/
example (a : A) : IsProperQuotient (oneItem {(0, (a, true))}) (oneItem ∅) := by
  -- A free item imposes no equation.
  have hfree (v : Fin 1 → FreeGroup A) : v ∈ V (.id (FreeGroup A)) (oneItem ∅).toSystem :=
    (mem_V_toSystem_iff _).2 <| (forall_mem_equations _).2
      ⟨fun μ ↦ μ.elim0, fun _ hb ↦ absurd hb (Finset.notMem_empty _),
        fun _ hc ↦ absurd hc (Finset.notMem_empty _)⟩
  have hV : V (.id (FreeGroup A)) (oneItem {(0, (a, true))}).toSystem ⊆
      V (.id (FreeGroup A)) (oneItem ∅).toSystem := fun v _ ↦ hfree v
  refine ⟨CoordGroup.homOfVSubset hV, CoordGroup.homOfVSubset_surjective hV, fun hinj ↦ ?_⟩
  -- The equation `h₀ a⁻¹` vanishes on the solutions of `h₀ = a` but not at `h₀ = 1`.
  let w : GX (FreeGroup A) (Fin 1) := inr (FreeGroup.of 0) * inl (FreeGroup.of a)⁻¹
  have hw : w ∈ Rad (.id (FreeGroup A)) (oneItem {(0, (a, true))}).toSystem :=
    mem_Rad.2 fun v hv ↦ by
      simpa [w, mul_inv_eq_one] using (mem_V_toSystem_iff _).1 hv _
        (coeffEquation_mem_equations _ (Finset.mem_singleton_self _))
  have h1 := (injective_iff_map_eq_one _).1 hinj _
    ((CoordGroup.homOfVSubset_mk hV w).trans ((QuotientGroup.eq_one_iff w).2 hw))
  simpa [w] using mem_Rad.1 ((QuotientGroup.eq_one_iff w).1 h1) 1 (hfree 1)

end TauCeti.GenEq
