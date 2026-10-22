/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Comodules over linearly reductive coalgebras are semisimple

A coalgebra over a field is linearly reductive when its finite-dimensional comodules are
completely reducible. This file shows that the finiteness restriction is harmless: over a
linearly reductive coalgebra **every** comodule is completely reducible, and is the sum of its
simple subcomodules. Applied to the regular comodule, this says that a linearly reductive
coalgebra is cosemisimple: it is the sum of its simple right coideals, and hence it is spanned
by the matrix coefficients of its simple comodules. For the coordinate Hopf algebra `O(G)` of a
linearly reductive affine group, this is the spanning part of the algebraic Peter--Weyl
decomposition of `O(G)` into the coefficient spaces of the irreducible representations; the
independence of these spaces is not proved here.

The passage from finite to arbitrary comodules uses the usual Zorn argument for modules that are
sums of semisimple submodules, as in Mathlib's `complementedLattice_of_sSup_atoms_eq_top`. That
theorem needs a modular complete lattice, while subcomodules only form a complete
join-semilattice here, so the argument is carried out directly: intersections with a
subcomodule `F` are formed as inverse images along the inclusion of `F`, and disjointness is
tested on underlying submodules. Over a field every element lies in a
finite-dimensional subcomodule, so the finite-dimensional subcomodules supply the required
family of completely reducible subcomodules.

## Main declarations

* `TauCeti.Comodule.isCompletelyReducible_of_sSup_eq_top`: over a commutative ring and a flat
  coalgebra, a comodule which is the supremum of completely reducible subcomodules is completely
  reducible.
* `TauCeti.Comodule.isCompletelyReducible_of_forall_finite`: over a field, a comodule is
  completely reducible as soon as its finite-dimensional subcomodules are.
* `TauCeti.Comodule.isCompletelyReducible_of_isLinearlyReductive`: **every comodule over a
  linearly reductive coalgebra is completely reducible**, with no finiteness assumption.
* `TauCeti.Subcomodule.instIsAtomic`: over a field every nonzero subcomodule contains a simple
  subcomodule, and `TauCeti.Subcomodule.finite_of_isAtom`: simple subcomodules are
  finite-dimensional.
* `TauCeti.Subcomodule.isCompletelyReducible_of_isAtom`: a simple subcomodule is completely
  reducible.
* `TauCeti.Comodule.isCompletelyReducible_iff_sSup_isAtom_eq_top`: over a field, a comodule is
  completely reducible exactly when it is the sum of its simple subcomodules.
* `TauCeti.Coalgebra.IsLinearlyReductive.iSup_matrixCoefficientSubmodule_eq_top`: **a linearly
  reductive coalgebra is spanned by the matrix coefficients of its simple subcomodules.**

## References

* M. Sweedler, *Hopf Algebras* (1969), on cosemisimple coalgebras.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 12 (linearly reductive groups).
-/

public section

open Module

namespace TauCeti

universe u v w

namespace Comodule

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable {V : Type w} [AddCommGroup V] [Module R V] [Comodule R C V]

/-- Let `Q` be maximal among the subcomodules meeting `W` trivially. Then `W ⊔ Q` contains every
completely reducible subcomodule `F`: otherwise a complement in `F` of `F ∩ (W ⊔ Q)` could be
added to `Q`. -/
private theorem le_sup_of_maximal_disjoint {W Q : Subcomodule R C V}
    (hQ : Maximal (fun Q : Subcomodule R C V ↦ Disjoint W.toSubmodule Q.toSubmodule) Q)
    (F : Subcomodule R C V) (hF : IsCompletelyReducible R C F) : F ≤ W ⊔ Q := by
  -- `X` is `F ∩ (W ⊔ Q)`, seen inside `F`, and `Y` is a complement of it in `F`.
  let X := (W ⊔ Q).comap (Subcomodule.subtype F)
  obtain ⟨Y, hY⟩ := hF.exists_isCompl X
  let Y' := Y.map (Subcomodule.subtype F)
  have hY'dis : Disjoint (W ⊔ Q).toSubmodule Y'.toSubmodule := by
    refine Submodule.disjoint_def.mpr fun v hv hv' ↦ ?_
    obtain ⟨y, hyY, rfl⟩ := Subcomodule.mem_map.mp hv'
    have hyX : y ∈ X := Subcomodule.mem_comap.mpr hv
    simpa using Submodule.disjoint_def.mp hY.disjoint y hyX hyY
  -- `Q ⊔ Y'` still meets `W` trivially, so it is `Q` by maximality.
  have hdis : Disjoint W.toSubmodule (Q ⊔ Y').toSubmodule := by
    rw [Subcomodule.sup_toSubmodule]
    exact hQ.1.disjoint_sup_right_of_disjoint_sup_left
      (by rwa [← Subcomodule.sup_toSubmodule])
  have hY'Q : Y' ≤ Q := le_sup_right.trans (hQ.2 hdis le_sup_left)
  have hYbot : Y.toSubmodule = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun y hy ↦ Subtype.ext ?_
    have hy' : (y : V) ∈ Y' := by
      simpa using Subcomodule.mem_map_of_mem (Subcomodule.subtype F) hy
    exact Submodule.disjoint_def.mp hY'dis _ ((le_sup_right : Q ≤ W ⊔ Q) (hY'Q hy')) hy'
  have hX : X.toSubmodule = ⊤ := by simpa [hYbot] using hY.sup_eq_top
  intro v hv
  simpa using Subcomodule.mem_comap.mp (hX ▸ Submodule.mem_top : (⟨v, hv⟩ : F) ∈ X.toSubmodule)

/-- **A sum of completely reducible subcomodules is completely reducible.** If a family of
subcomodules, each completely reducible as a comodule in its own right, has supremum the whole
comodule, then the comodule is completely reducible. -/
theorem isCompletelyReducible_of_sSup_eq_top {S : Set (Subcomodule R C V)} (hS : sSup S = ⊤)
    (hcr : ∀ F ∈ S, IsCompletelyReducible R C F) : IsCompletelyReducible R C V := by
  refine IsCompletelyReducible.of_exists_isCompl fun W ↦ ?_
  -- A subcomodule maximal among those meeting `W` trivially is a complement of `W`.
  obtain ⟨Q, hQ⟩ :=
    zorn_le₀ {Q : Subcomodule R C V | Disjoint W.toSubmodule Q.toSubmodule} fun c hc hchain ↦ by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, by simp, by simp⟩
      refine ⟨sSup c, Submodule.disjoint_def.mpr fun v hvW hv ↦ ?_, fun _ hz ↦ le_sSup hz⟩
      obtain ⟨N, hN, hvN⟩ :=
        (Subcomodule.mem_sSup_of_directedOn hne hchain.directedOn).mp hv
      exact Submodule.disjoint_def.mp (hc hN) v hvW hvN
  refine ⟨Q, hQ.1, codisjoint_iff.mpr ?_⟩
  rw [← Subcomodule.sup_toSubmodule, Subcomodule.toSubmodule_eq_top, eq_top_iff, ← hS]
  exact sSup_le fun F hF ↦ le_sup_of_maximal_disjoint hQ F (hcr F hF)

end Ring

end Comodule

namespace Subcomodule

section Semiring

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R C V]

/-- A simple subcomodule is completely reducible, as a comodule in its own right. -/
theorem isCompletelyReducible_of_isAtom {S : Subcomodule R C V}
    (hS : IsAtom S) : Comodule.IsCompletelyReducible R C S := by
  refine Comodule.isCompletelyReducible_of_forall_eq_bot_or_eq_top fun Z ↦ ?_
  -- The image of `Z` in `V` lies below the atom `S`, so it is `⊥` or `S`.
  rcases hS.le_iff.mp (map_le_iff.mpr fun x _ ↦ by simp : Z.map (subtype S) ≤ S)
    with h | h
  · refine Or.inl (eq_bot_iff.mpr fun z hz ↦ mem_bot.mpr (Subtype.ext ?_))
    have hz' := mem_map_of_mem (subtype S) hz
    rw [h, mem_bot] at hz'
    simpa using hz'
  · refine Or.inr (eq_top_iff.mpr fun s _ ↦ ?_)
    obtain ⟨z, hz, hzs⟩ := mem_map.mp (h.symm ▸ s.2 : (s : V) ∈ Z.map (subtype S))
    rwa [← Subtype.ext (by simpa using hzs : (z : V) = s)]

end Semiring

section Field

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {V : Type w} [AddCommGroup V] [Module k V] [Comodule k C V]

/-- **Every nonzero subcomodule over a field contains a simple subcomodule.** A nonzero
finite-dimensional subcomodule of minimal dimension inside it is simple. -/
instance instIsAtomic : IsAtomic (Subcomodule k C V) := by
  refine ⟨fun b ↦ or_iff_not_imp_left.mpr fun hb ↦ ?_⟩
  obtain ⟨v, hvb, hv0⟩ := ne_bot_iff.mp hb
  obtain ⟨F, hFb, hF, hvF⟩ := exists_finite_le_of_mem hvb
  obtain ⟨A, ⟨hAF, hA0⟩, hmin⟩ :=
    (measure fun A : Subcomodule k C V ↦ finrank k A.toSubmodule).wf.has_min
      {A | A ≤ F ∧ A ≠ ⊥} ⟨F, le_rfl, ne_bot_iff.mpr ⟨v, hvF, hv0⟩⟩
  refine ⟨A, ⟨hA0, fun B hBA ↦ by_contra fun hB0 ↦ ?_⟩, hAF.trans hFb⟩
  have : Module.Finite k A.toSubmodule :=
    Submodule.finiteDimensional_of_le (toSubmodule_le_toSubmodule.mpr hAF)
  exact hmin B ⟨hBA.le.trans hAF, hB0⟩ (Submodule.finrank_lt_finrank_of_lt hBA)

/-- A simple subcomodule over a field is finite-dimensional. -/
theorem finite_of_isAtom {S : Subcomodule k C V} (hS : IsAtom S) : Module.Finite k S := by
  obtain ⟨v, hvS, hv0⟩ := ne_bot_iff.mp hS.1
  obtain ⟨F, hFS, hF, hvF⟩ := exists_finite_le_of_mem hvS
  rw [← (hS.le_iff.mp hFS).resolve_left (ne_bot_iff.mpr ⟨v, hvF, hv0⟩)]
  exact hF

end Field

end Subcomodule

namespace Comodule

section Field

variable {k : Type u} [Field k]

section Group

variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {V : Type w} [AddCommGroup V] [Module k V] [Comodule k C V]

/-- Over a field, a comodule whose finite-dimensional subcomodules are completely reducible is
completely reducible. -/
theorem isCompletelyReducible_of_forall_finite
    (h : ∀ F : Subcomodule k C V, Module.Finite k F → IsCompletelyReducible k C F) :
    IsCompletelyReducible k C V :=
  isCompletelyReducible_of_sSup_eq_top Subcomodule.sSup_finiteSubcomodules_eq_top
    fun F hF ↦ h F (Subcomodule.mem_finiteSubcomodules.mp hF)

/-- **Complete reducibility as a sum of simple subcomodules.** Over a field, a comodule is
completely reducible exactly when it is the supremum of its simple subcomodules. -/
theorem isCompletelyReducible_iff_sSup_isAtom_eq_top :
    IsCompletelyReducible k C V ↔ sSup {S : Subcomodule k C V | IsAtom S} = ⊤ := by
  refine ⟨fun hV ↦ ?_, fun h ↦ isCompletelyReducible_of_sSup_eq_top h
    fun _ hS ↦ Subcomodule.isCompletelyReducible_of_isAtom hS⟩
  -- A complement of the sum of the simple subcomodules contains no simple subcomodule.
  obtain ⟨Q, hQ⟩ := hV.exists_isCompl (sSup {S : Subcomodule k C V | IsAtom S})
  rcases eq_bot_or_exists_atom_le Q with rfl | ⟨A, hA, hAQ⟩
  · have h := hQ.sup_eq_top
    rwa [Subcomodule.bot_toSubmodule, sup_bot_eq, Subcomodule.toSubmodule_eq_top] at h
  · refine absurd ?_ hA.1
    rw [← Subcomodule.toSubmodule_eq_bot, ← le_bot_iff, ← hQ.inf_eq_bot]
    exact le_inf (Subcomodule.toSubmodule_le_toSubmodule.mpr (le_sSup hA))
      (Subcomodule.toSubmodule_le_toSubmodule.mpr hAQ)

end Group

/-- **Every comodule over a linearly reductive coalgebra is completely reducible.** Linear
reductivity only asks for complete reducibility of finite-dimensional comodules, as in
`TauCeti.Coalgebra.IsLinearlyReductive.isCompletelyReducible`; this removes the finiteness
assumption, so it applies for instance to the regular comodule. -/
theorem isCompletelyReducible_of_isLinearlyReductive
    {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C]
    {V : Type w} [AddCommMonoid V] [Module k V] [Comodule k C V]
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) : IsCompletelyReducible k C V := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact isCompletelyReducible_of_forall_finite fun _ _ ↦ hC.isCompletelyReducible

/-- Every comodule over a linearly reductive coalgebra is the sum of its simple subcomodules. -/
theorem sSup_isAtom_eq_top_of_isLinearlyReductive
    {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    {V : Type w} [AddCommGroup V] [Module k V] [Comodule k C V]
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) :
    sSup {S : Subcomodule k C V | IsAtom S} = ⊤ :=
  isCompletelyReducible_iff_sSup_isAtom_eq_top.mp (isCompletelyReducible_of_isLinearlyReductive hC)

end Field

end Comodule

namespace Coalgebra.IsLinearlyReductive

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- **A linearly reductive coalgebra is cosemisimple:** it is spanned by the matrix coefficients
of its simple subcomodules, that is, of its simple right coideals. Each of these is
finite-dimensional by `TauCeti.Subcomodule.finite_of_isAtom`. -/
theorem iSup_matrixCoefficientSubmodule_eq_top (hC : IsLinearlyReductive.{u, v, u} k C) :
    ⨆ (S : Subcomodule k C C) (_ : IsAtom S),
      Comodule.matrixCoefficientSubmodule (R := k) (C := C) (M := S) = ⊤ := by
  rw [eq_top_iff, ← Subcomodule.top_toSubmodule (R := k) (C := C) (M := C),
    ← Comodule.sSup_isAtom_eq_top_of_isLinearlyReductive hC, Subcomodule.sSup_toSubmodule]
  exact iSup_le fun S ↦
    S.1.toSubmodule_le_matrixCoefficientSubmodule.trans (le_iSup₂_of_le S.1 S.2 le_rfl)

end Coalgebra.IsLinearlyReductive

end TauCeti
