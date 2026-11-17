/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import Mathlib.Data.Set.Card
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# Uniqueness of dominant neutral elements in `Int(L)`-orbits

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra, and `b` a base of the root system
of `H`. The file `TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant` shows that every `Int(L)`-orbit
of neutral elements of `sl₂` triples meets the finite set `b.dominantNeutralElements`. This file
proves that the dominant representative in each orbit is **unique**.

The argument runs in two steps. First, by Chevalley's restriction theorem and Weyl-orbit separation
(`LieSubalgebra.forall_mem_lieInvariants_lift_eval_eq_iff_exists_coweightEquiv`), two elements of
`H` taking the same value on every Lie-invariant polynomial function in `S(L*)^L` lie in the same
Weyl orbit. Second, over any integral domain of characteristic zero, a Weyl orbit of integral
coweights contains at most one dominant representative
(`RootPairing.Base.eq_of_coweightEquiv_eq_of_forall_exists_nat_root'`). Combining these two steps
gives `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq`, which requires
only agreement on Lie-invariant polynomials and therefore applies equally to `Int(L)`-conjugacy and
to the adjoint action of a connected linear algebraic group.

For `Int(L)` itself, it follows that `h ↦ MulAction.orbit (intLieAlgebra K L) (h : L)` maps
`b.dominantNeutralElements` bijectively onto the `Int(L)`-orbits of neutral elements of `sl₂`
triples, and by Kostant's conjugacy theorem (`IsSl2Triple.exists_lieEquiv_apply_eq`), two `sl₂`
triples with `Int(L)`-conjugate nilpositive elements and dominant neutral elements share the same
neutral element.

## Main results

* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq`: two dominant neutral
  elements taking the same value on every invariant polynomial in `S(L*)^L` are equal.
* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra`: two `Int(L)`-conjugate
  dominant neutral elements are equal.
* `RootPairing.Base.injOn_orbit_dominantNeutralElements` and
  `RootPairing.Base.bijOn_orbit_dominantNeutralElements`: `h ↦ orbit (Int L) (h : L)` is a
  bijection from `b.dominantNeutralElements` onto the `Int(L)`-orbits of neutral elements of `sl₂`
  triples.
* `RootPairing.Base.existsUnique_mem_dominantNeutralElements_of_isSl2Triple`: the neutral element of
  every `sl₂` triple is `Int(L)`-conjugate to a unique dominant neutral element in `H`.
* `RootPairing.Base.ncard_image_orbit_setOf_exists_isSl2Triple_eq`: the number of `Int(L)`-orbits
  of neutral elements equals `(b.dominantNeutralElements).ncard`.
* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_intLieAlgebra_smul_eq`: if two `sl₂`
  triples have dominant neutral elements and `Int(L)`-conjugate nilpositive elements, their neutral
  elements coincide.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. 81 (1959), 973–1032.
-/

public section

namespace RootPairing.Base

open LieAlgebra LieAlgebra.IsKilling LieModule Module TauCeti TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  (b : (rootSystem H).Base)

/-- **Dominant neutral elements are separated by Lie-invariant polynomials.** If two dominant
neutral elements in `H` take the same value on every invariant polynomial function in `S(L*)^L`,
then they are equal. -/
theorem eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq
    {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (heq : ∀ p ∈ lieInvariants K L (Dual K L),
      _root_.SymmetricAlgebra.lift (Dual.eval K L (h₁ : L)) p =
        _root_.SymmetricAlgebra.lift (Dual.eval K L (h₂ : L)) p) :
    h₁ = h₂ := by
  obtain ⟨w, hw⟩ := H.forall_mem_lieInvariants_lift_eval_eq_iff_exists_coweightEquiv.mp heq
  exact b.eq_of_coweightEquiv_eq_of_forall_exists_nat_root' hw
    ((b.mem_dominantNeutralElements_iff h₁).mp hh₁).2
    ((b.mem_dominantNeutralElements_iff h₂).mp hh₂).2

section IntLieAlgebra

variable [LieAlgebra ℚ L]

/-- **Two `Int(L)`-conjugate dominant neutral elements are equal.** -/
theorem eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra
    {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L)
    (hgh : g • (h₁ : L) = h₂) :
    h₁ = h₂ := by
  refine b.eq_of_mem_dominantNeutralElements_of_forall_lift_eval_eq hh₁ hh₂ fun p hp ↦ ?_
  rw [← hgh, lift_eval_smul_of_mem_intLieAlgebra hg hp]

/-- Distinct dominant neutral elements lie in distinct `Int(L)`-orbits. -/
theorem injOn_orbit_dominantNeutralElements :
    Set.InjOn (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L))
      b.dominantNeutralElements := by
  intro h₁ hh₁ h₂ hh₂ horb
  dsimp only at horb
  have hmem : (h₂ : L) ∈ MulAction.orbit (intLieAlgebra K L) (h₁ : L) := by
    rw [horb]
    exact MulAction.mem_orbit_self _
  obtain ⟨⟨g, hg⟩, hgh⟩ := hmem
  exact b.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra hh₁ hh₂ hg hgh

/-- **`Int(L)`-orbits of neutral elements are in bijection with dominant neutral elements.** -/
theorem bijOn_orbit_dominantNeutralElements :
    Set.BijOn (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L))
      b.dominantNeutralElements
      (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}) :=
  ⟨fun h hh ↦ ⟨(h : L), ((b.mem_dominantNeutralElements_iff h).mp hh).1, rfl⟩,
    b.injOn_orbit_dominantNeutralElements,
    b.image_orbit_dominantNeutralElements.superset⟩

/-- **Unique dominant representative.** The neutral element of every `sl₂` triple is
`Int(L)`-conjugate to a unique dominant neutral element in `H` for the base `b`. -/
theorem existsUnique_mem_dominantNeutralElements_of_isSl2Triple
    {h e f : L} (t : IsSl2Triple h e f) :
    ∃! h' : H, h' ∈ b.dominantNeutralElements ∧
      ∃ g ∈ intLieAlgebra K L, g • h = (h' : L) := by
  obtain ⟨g₁, hg₁, h', hh', hg₁h, -⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  refine ⟨h', ⟨hh', g₁, hg₁, hg₁h⟩, ?_⟩
  rintro h'' ⟨hh'', g₂, hg₂, hg₂h⟩
  refine (b.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra hh' hh''
    (mul_mem hg₂ (inv_mem hg₁)) ?_).symm
  rw [mul_smul, ← hg₁h, inv_smul_smul, hg₂h]

/-- **Exact count of `Int(L)`-orbits of neutral elements.** The number of `Int(L)`-orbits of
neutral elements of `sl₂` triples equals the number of dominant neutral elements in `H`. -/
theorem ncard_image_orbit_setOf_exists_isSl2Triple_eq :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.image_orbit_dominantNeutralElements, b.injOn_orbit_dominantNeutralElements.ncard_image]

/-- **Well-definedness of the dominant neutral element attached to an `Int(L)`-orbit of nilpotent
elements.** If two `sl₂` triples have dominant neutral elements in `H` and `Int(L)`-conjugate
nilpositive elements, then their neutral elements are equal. -/
theorem eq_of_mem_dominantNeutralElements_of_intLieAlgebra_smul_eq
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L)
    (hge : g • e₁ = e₂) :
    h₁ = h₂ := by
  have t₁' : IsSl2Triple (g • (h₁ : L)) e₂ (g • f₁) := by
    rw [← hge]
    exact t₁.smul_of_mem_intLieAlgebra hg
  obtain ⟨φ, hφ, -, hφh, -⟩ := t₁'.exists_lieEquiv_apply_eq (K := K) t₂
  set gφ : LinearMap.GeneralLinearGroup K L :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K L).symm φ.toLinearEquiv
  have hgφ : gφ ∈ intLieAlgebra K L :=
    map_expAdSubgroup_le_intLieAlgebra e₂ ⟨φ.toLinearEquiv, hφ, rfl⟩
  refine b.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra hh₁ hh₂ (mul_mem hgφ hg) ?_
  rw [mul_smul]
  exact hφh

end IntLieAlgebra

end RootPairing.Base
