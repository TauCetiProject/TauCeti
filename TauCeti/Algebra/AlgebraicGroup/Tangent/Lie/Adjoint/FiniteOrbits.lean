/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov

/-!
# Finiteness and cardinality bounds for nilpotent adjoint orbits

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)` has
nondegenerate Killing form. Fix a Cartan subalgebra `𝔥 ≤ 𝔤` and a base `b` of its root system.

Combining three ingredients established in `TauCeti`:

1. Lie-algebraic reduction of `sl₂` triples and nonzero `ad`-nilpotent elements into the finite set
   `b.dominantNeutralElements` under `Int(𝔤)`
   (`IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed` and
   `TauCeti.exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad`);
2. realization of `Int(𝔤)` inside the adjoint action of `G°(k)`
   (`TauCeti.exists_mem_identityComponentHopfIdeal_ofLinearEquiv_basePointsAdjointLieEquiv_eq`);
3. Malcev–Kostant conjugacy at fixed neutral element inside `C_G(h)°(k) ≤ G°(k)`
   (`IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq`
   together with `TauCeti.HopfIdeal.identityComponentHopfIdeal_le_identityComponent`),

every nonzero `ad`-nilpotent element of `𝔤` lies in the `G°(k)`-orbit of one of at most
`3 ^ Module.finrank k 𝔥` chosen nilpositive representatives indexed by `b.dominantNeutralElements`.

Consequently:

* for *every* subgroup `Γ ≤ G(k)` containing `G°(k)` — in particular for `G°(k)` itself — there are
  only finitely many nilpotent `Γ`-orbits in `𝔤`: at most `3 ^ finrank k 𝔥` nonzero orbits and at
  most `3 ^ finrank k 𝔥 + 1` in total;
* the rational `G(k)`-orbits (`TauCeti.Comodule.VectorOrbit`) and their topological orbit images
  (`TauCeti.Comodule.VectorOrbit.image`) in `P(𝔤 × k)` of `ad`-nilpotent elements (and, when `G` is
  connected, of the rational points of the nilpotent cone `TauCeti.nilpotentConeIdeal k H`) are
  likewise finite in number, bounded by `3 ^ finrank k 𝔥` (nonzero) and `3 ^ finrank k 𝔥 + 1`
  (all).

## Main declarations

* `IsSl2Triple.exists_mem_identityComponentHopfIdeal_dominantNeutralElements`: every `sl₂` triple
  in `𝔤` is conjugate under `G°(k)` to one whose neutral element lies in
  `b.dominantNeutralElements`.
* `TauCeti.exists_mem_identityComponentHopfIdeal_isSl2Triple_of_isNilpotent_ad`: every nonzero
  `ad`-nilpotent element of `𝔤` is conjugate under `G°(k)` to the nilpositive element of an `sl₂`
  triple with neutral element in `b.dominantNeutralElements`.
* `TauCeti.exists_finite_subset_isNilpotent_ad_ncard_le`: existence of a finite set `S ⊆ 𝔤` of at
  most `3 ^ finrank k 𝔥` nonzero `ad`-nilpotent representatives meeting every nonzero nilpotent
  `G°(k)`-orbit.
* `TauCeti.finite_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad`,
  `TauCeti.ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_ne_zero_le`,
  and `TauCeti.ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_le`:
  finiteness and the `3 ^ rank` / `3 ^ rank + 1` bounds for nilpotent `Γ`-orbits in `𝔤` whenever
  `G°(k) ≤ Γ ≤ G(k)`, with specialization to `G°(k)`.
* `TauCeti.finite_image_vectorOrbit_mk_setOf_isNilpotent_ad`,
  `TauCeti.ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero_le`, and
  `TauCeti.ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_le`: finiteness and bounds for rational
  nilpotent `G(k)`-orbits in `TauCeti.Comodule.VectorOrbit`.
* `TauCeti.finite_image_vectorOrbit_image_mk_setOf_isNilpotent_ad`,
  `TauCeti.ncard_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_ne_zero_le`,
  `TauCeti.ncard_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_le`, and
  `TauCeti.finite_image_vectorOrbit_image_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval`:
  finiteness and cardinality bounds for topological adjoint `G`-orbit images in `P(𝔤 × k)`.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
* R. W. Richardson, *Conjugacy classes in Lie algebras and algebraic groups*, Ann. of Math. (2)
  **86** (1967), 1–15.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold (1993), Theorem 3.2.10 and §3.5.
-/

public section

open WithConv

namespace IsSl2Triple

open TauCeti

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

attribute [local instance] Derivation.adjointComodule

/-- **Group-level dominant conjugation of `sl₂` triples.** Over an algebraically closed field `k`
of characteristic zero, if `G = Spec H` is of finite type with Killing Lie algebra `𝔤`, every `sl₂`
triple `(h, e, f)` in `𝔤` is conjugate by a rational point of `G°` to an `sl₂` triple whose neutral
element lies in `b.dominantNeutralElements`. -/
theorem exists_mem_identityComponentHopfIdeal_dominantNeutralElements
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h' ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h =
            (h' : Module.Dual k (Bialgebra.CotangentSpace k H)) ∧
          IsSl2Triple (h' : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
              f) := by
  let _ : LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    TauCeti.ratLieAlgebra k _
  obtain ⟨φ, hφ, h', hh', hφh, t'⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, -, hg₀, -, happ⟩ :=
    exists_mem_identityComponentHopfIdeal_ofLinearEquiv_basePointsAdjointLieEquiv_eq (H := H) hφ
  refine ⟨g, hg₀, h', hh', (happ h).trans hφh, ?_⟩
  simpa only [happ] using t'

end IsSl2Triple

namespace TauCeti

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

attribute [local instance] Derivation.adjointComodule

section Representatives

variable {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))}
  [𝔥.IsCartanSubalgebra]

/-- **Every nonzero nilpotent element is `G°(k)`-conjugate into a dominant `sl₂` triple.** Over an
algebraically closed field `k` of characteristic zero, every nonzero `ad`-nilpotent `e ∈ 𝔤` is
carried by some `g ∈ G°(k)` to the nilpositive element of an `sl₂` triple whose neutral element
lies in `b.dominantNeutralElements`. -/
theorem exists_mem_identityComponentHopfIdeal_isSl2Triple_of_isNilpotent_ad
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h ∈ b.dominantNeutralElements,
        ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
          IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) f := by
  let _ : LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    TauCeti.ratLieAlgebra k _
  obtain ⟨φ, hφ, h, hh, f, t⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  obtain ⟨g, -, hg₀, -, happ⟩ :=
    exists_mem_identityComponentHopfIdeal_ofLinearEquiv_basePointsAdjointLieEquiv_eq (H := H) hφ
  exact ⟨g, hg₀, h, hh, f, by simpa only [happ] using t⟩

/-- **Finite set of `G°(k)`-representatives for nonzero nilpotent elements.** Given a base `b` of
the root system of a Cartan subalgebra `𝔥 ≤ 𝔤`, there is a finite subset `S ⊆ 𝔤` of cardinality at
most `3 ^ finrank k 𝔥` consisting of nonzero `ad`-nilpotent elements such that every nonzero
`ad`-nilpotent `e ∈ 𝔤` lies in the `G°(k)`-orbit of some element of `S`. -/
theorem exists_finite_subset_isNilpotent_ad_ncard_le
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    ∃ S : Set (Module.Dual k (Bialgebra.CotangentSpace k H)),
      S.Finite ∧ S.ncard ≤ 3 ^ Module.finrank k 𝔥 ∧
      (∀ x ∈ S,
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x) ∧ x ≠ 0) ∧
      ∀ e : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) → e ≠ 0 →
        ∃ x ∈ S, ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
          Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = x := by
  let 𝔤 := Module.Dual k (Bialgebra.CotangentSpace k H)
  let rep : b.dominantNeutralElements → 𝔤 := fun h =>
    Classical.choose ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  have hrep : ∀ h : b.dominantNeutralElements, ∃ f : 𝔤, IsSl2Triple (h.1 : 𝔤) (rep h) f :=
    fun h => Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  have : Finite b.dominantNeutralElements := b.finite_dominantNeutralElements.to_subtype
  have huniv : (Set.univ : Set b.dominantNeutralElements).ncard =
      b.dominantNeutralElements.ncard := by
    simp
  refine ⟨Set.range rep, Set.finite_range rep, ?_, ?_, ?_⟩
  · rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans
      (huniv.trans_le b.ncard_dominantNeutralElements_le)
  · rintro _ ⟨h, rfl⟩
    obtain ⟨f₀, t₀⟩ := hrep h
    exact ⟨t₀.isNilpotent_toEnd_e (K := k) (M := 𝔤), t₀.e_ne_zero⟩
  · intro e he he0
    obtain ⟨g₁, hg₁, h, hh, f₁, t₁⟩ :=
      exists_mem_identityComponentHopfIdeal_isSl2Triple_of_isNilpotent_ad (H := H) b he he0
    obtain ⟨f₀, t₀⟩ := hrep ⟨h, hh⟩
    obtain ⟨g₂, hg₂, -, hg₂e, -⟩ :=
      t₁.exists_mem_quotientPointsSubgroup_identityComponent_basePointsRepresentation_eq t₀
    have hg₂₀ : g₂ ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) := by
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg₂ ⊢
      exact fun x hx => hg₂ x
        ((centralizerHopfIdeal H (h : 𝔤)).identityComponentHopfIdeal_le_identityComponent hx)
    refine ⟨rep ⟨h, hh⟩, Set.mem_range_self (⟨h, hh⟩ : b.dominantNeutralElements),
      g₂ * g₁, Subgroup.mul_mem _ hg₂₀ hg₁, ?_⟩
    rw [map_mul, mul_apply_eq_comp, hg₂e]

end Representatives

section PointOrbits

/-- Any map `orb : 𝔤 → α` constant on `G°(k)`-orbits sends the nonzero `ad`-nilpotent elements of
`𝔤` onto a finite set of cardinality at most `3 ^ finrank k 𝔥`. -/
private theorem finite_and_ncard_image_le_of_forall_eq {α : Type*}
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra]
    {orb : Module.Dual k (Bialgebra.CotangentSpace k H) → α}
    (horb : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ e : Module.Dual k (Bialgebra.CotangentSpace k H),
        orb (Comodule.basePointsRepresentation
          (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) = orb e) :
    (orb '' {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).Finite ∧
      (orb '' {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  obtain ⟨S, hSfin, hScard, hSnilp, hSsurj⟩ :=
    exists_finite_subset_isNilpotent_ad_ncard_le (H := H) b
  have heq : orb '' {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
      IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
        e ≠ 0} = orb '' S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨e, ⟨he, he0⟩, rfl⟩
      obtain ⟨_, hxS, g, hg, rfl⟩ := hSsurj e he he0
      exact ⟨_, hxS, horb g hg e⟩
    · rintro _ ⟨x, hxS, rfl⟩
      exact ⟨x, hSnilp x hxS, rfl⟩
  rw [heq]
  exact ⟨hSfin.image orb, (Set.ncard_image_le hSfin).trans hScard⟩

/-- **Bound on nonzero nilpotent `Γ`-orbits in `Lie(G)`.** For any Cartan subalgebra `𝔥 ≤ 𝔤` and
any subgroup `Γ ≤ G(k)` containing `G°(k)`, there are at most `3 ^ finrank k 𝔥` nonzero nilpotent
`Γ`-orbits in `𝔤`. -/
theorem ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_ne_zero_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra]
    {Γ : Subgroup (WithConv (H →ₐ[k] k))}
    (hΓ : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤ Γ) :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun γ : Γ => Comodule.basePointsRepresentation
          (Module.Dual k (Bialgebra.CotangentSpace k H)) γ.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).ncard ≤
      3 ^ Module.finrank k 𝔥 := by
  let 𝔤 := Module.Dual k (Bialgebra.CotangentSpace k H)
  let _ : MulAction Γ 𝔤 := MulAction.compHom 𝔤
    ((Representation.asGroupHom (Comodule.basePointsRepresentation 𝔤)).comp Γ.subtype)
  exact (finite_and_ncard_image_le_of_forall_eq (H := H) 𝔥
    fun g hg e => MulAction.orbit_smul (⟨g, hΓ hg⟩ : Γ) e).2

/-- **Finiteness of nonzero nilpotent `Γ`-orbits in `Lie(G)`.** -/
theorem finite_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_ne_zero
    {Γ : Subgroup (WithConv (H →ₐ[k] k))}
    (hΓ : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤ Γ) :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun γ : Γ => Comodule.basePointsRepresentation
          (Module.Dual k (Bialgebra.CotangentSpace k H)) γ.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).Finite := by
  let 𝔤 := Module.Dual k (Bialgebra.CotangentSpace k H)
  let _ : MulAction Γ 𝔤 := MulAction.compHom 𝔤
    ((Representation.asGroupHom (Comodule.basePointsRepresentation 𝔤)).comp Γ.subtype)
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤
  exact (finite_and_ncard_image_le_of_forall_eq (H := H) (LieSubalgebra.engel k x)
    fun g hg e => MulAction.orbit_smul (⟨g, hΓ hg⟩ : Γ) e).1

/-- **Finiteness of nilpotent `Γ`-orbits in `Lie(G)`.** Over an algebraically closed field of
characteristic zero, if `𝔤 = Lie(G)` is Killing and `G°(k) ≤ Γ ≤ G(k)`, there are only finitely
many nilpotent `Γ`-orbits in `𝔤`. -/
theorem finite_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad
    {Γ : Subgroup (WithConv (H →ₐ[k] k))}
    (hΓ : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤ Γ) :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun γ : Γ => Comodule.basePointsRepresentation
          (Module.Dual k (Bialgebra.CotangentSpace k H)) γ.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).Finite := by
  have h0 : (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ∈
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by simp
  rw [← Set.insert_sdiff_self_of_mem h0, Set.image_insert_eq]
  exact
    (finite_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_ne_zero hΓ).insert _

/-- **Bound on all nilpotent `Γ`-orbits in `Lie(G)`.** For any Cartan subalgebra `𝔥 ≤ 𝔤` and any
subgroup `Γ ≤ G(k)` containing `G°(k)`, there are at most `3 ^ finrank k 𝔥 + 1` nilpotent
`Γ`-orbits in `𝔤`. -/
theorem ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra]
    {Γ : Subgroup (WithConv (H →ₐ[k] k))}
    (hΓ : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤ Γ) :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun γ : Γ => Comodule.basePointsRepresentation
          (Module.Dual k (Bialgebra.CotangentSpace k H)) γ.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 := by
  have h0 : (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ∈
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by simp
  rw [← Set.insert_sdiff_self_of_mem h0, Set.image_insert_eq]
  exact (Set.ncard_insert_le _ _).trans <| Nat.add_le_add_right
    (ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_ne_zero_le 𝔥 hΓ) 1

/-- **Finiteness of nilpotent `G°(k)`-orbits in `Lie(G)`.** -/
theorem finite_image_range_identityComponentHopfIdeal_setOf_isNilpotent_ad :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun g : CommHopfAlgCat.quotientPointsSubgroup H.obj
            (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) =>
          Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).Finite :=
  finite_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad (H := H) le_rfl

/-- **`3 ^ rank + 1` bound on nilpotent `G°(k)`-orbits in `Lie(G)`.** -/
theorem ncard_image_range_identityComponentHopfIdeal_setOf_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        Set.range fun g : CommHopfAlgCat.quotientPointsSubgroup H.obj
            (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) =>
          Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g.1 e) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 :=
  ncard_image_range_subgroup_basePointsRepresentation_setOf_isNilpotent_ad_le (H := H) 𝔥 le_rfl

/-- **Bound on nonzero rational nilpotent `G(k)`-orbits in `Lie(G)`.** -/
theorem ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((Comodule.VectorOrbit.mk (k := k) (H := H) :
        Module.Dual k (Bialgebra.CotangentSpace k H) → _) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).ncard ≤
      3 ^ Module.finrank k 𝔥 :=
  (finite_and_ncard_image_le_of_forall_eq (H := H) 𝔥
    fun g _ e => Comodule.VectorOrbit.mk_basePointsRepresentation g e).2

/-- **Finiteness of nonzero rational nilpotent `G(k)`-orbits in `Lie(G)`.** -/
theorem finite_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero :
    ((Comodule.VectorOrbit.mk (k := k) (H := H) :
        Module.Dual k (Bialgebra.CotangentSpace k H) → _) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k
    (Module.Dual k (Bialgebra.CotangentSpace k H))
  exact (finite_and_ncard_image_le_of_forall_eq (H := H) (LieSubalgebra.engel k x)
    fun g _ e => Comodule.VectorOrbit.mk_basePointsRepresentation g e).1

/-- **Finiteness of rational nilpotent `G(k)`-orbits in `Lie(G)`.** -/
theorem finite_image_vectorOrbit_mk_setOf_isNilpotent_ad :
    ((Comodule.VectorOrbit.mk (k := k) (H := H) :
        Module.Dual k (Bialgebra.CotangentSpace k H) → _) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).Finite := by
  have h0 : (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ∈
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by simp
  rw [← Set.insert_sdiff_self_of_mem h0, Set.image_insert_eq]
  exact (finite_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero (H := H)).insert _

/-- **`3 ^ rank + 1` bound on rational nilpotent `G(k)`-orbits in `Lie(G)`.** -/
theorem ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((Comodule.VectorOrbit.mk (k := k) (H := H) :
        Module.Dual k (Bialgebra.CotangentSpace k H) → _) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 := by
  have h0 : (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ∈
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by simp
  rw [← Set.insert_sdiff_self_of_mem h0, Set.image_insert_eq]
  exact (Set.ncard_insert_le _ _).trans <| Nat.add_le_add_right
    (ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero_le (H := H) 𝔥) 1

end PointOrbits

section SchemeOrbitImages

/-- **Bound on nonzero nilpotent topological adjoint `G`-orbit images.** For any Cartan subalgebra
`𝔥 ≤ 𝔤`, there are at most `3 ^ finrank k 𝔥` topological adjoint `G`-orbit images in `P(𝔤 × k)` of
nonzero `ad`-nilpotent elements. -/
theorem ncard_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_ne_zero_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).ncard ≤
      3 ^ Module.finrank k 𝔥 := by
  rw [← Set.image_image Comodule.VectorOrbit.image Comodule.VectorOrbit.mk]
  exact (Set.ncard_image_le
      (finite_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero (H := H))).trans
    (ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero_le (H := H) 𝔥)

/-- **Finiteness of nonzero nilpotent topological adjoint `G`-orbit images.** -/
theorem finite_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_ne_zero :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) ∧
          e ≠ 0}).Finite := by
  rw [← Set.image_image Comodule.VectorOrbit.image Comodule.VectorOrbit.mk]
  exact (finite_image_vectorOrbit_mk_setOf_isNilpotent_ad_ne_zero (H := H)).image _

/-- **Finiteness of nilpotent topological adjoint `G`-orbit images.** Over an algebraically closed
field of characteristic zero, if `𝔤 = Lie(G)` is Killing, the `ad`-nilpotent elements of `𝔤` have
only finitely many topological adjoint `G`-orbit images in `P(𝔤 × k)`. -/
theorem finite_image_vectorOrbit_image_mk_setOf_isNilpotent_ad :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).Finite := by
  rw [← Set.image_image Comodule.VectorOrbit.image Comodule.VectorOrbit.mk]
  exact (finite_image_vectorOrbit_mk_setOf_isNilpotent_ad (H := H)).image _

/-- **Bound on all nilpotent topological adjoint `G`-orbit images.** For any Cartan subalgebra
`𝔥 ≤ 𝔤`, there are at most `3 ^ finrank k 𝔥 + 1` topological adjoint `G`-orbit images in `P(𝔤 × k)`
of `ad`-nilpotent elements. -/
theorem ncard_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 := by
  rw [← Set.image_image Comodule.VectorOrbit.image Comodule.VectorOrbit.mk]
  exact (Set.ncard_image_le (finite_image_vectorOrbit_mk_setOf_isNilpotent_ad (H := H))).trans
    (ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_le (H := H) 𝔥)

/-- **Finiteness of adjoint `G`-orbit images on the nilpotent cone.** For a connected affine group
`G = Spec H` of finite type over an algebraically closed field of characteristic zero with Killing
Lie algebra `𝔤`, the rational points of the nilpotent cone `TauCeti.nilpotentConeIdeal k H` fall
into finitely many topological adjoint `G`-orbit images in `P(𝔤 × k)`. -/
theorem finite_image_vectorOrbit_image_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval
    [ConnectedSpace (PrimeSpectrum H)] :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        nilpotentConeIdeal k H ≤
          RingHom.ker
            (SymmetricAlgebra.lift
              (Module.Dual.eval k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))}).Finite := by
  simpa only [nilpotentConeIdeal_le_ker_lift_eval_iff] using
    finite_image_vectorOrbit_image_mk_setOf_isNilpotent_ad (H := H)

/-- **`3 ^ rank + 1` bound on adjoint `G`-orbit images on the nilpotent cone.** -/
theorem ncard_image_vectorOrbit_image_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval_le
    [ConnectedSpace (PrimeSpectrum H)]
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    ((fun e : Module.Dual k (Bialgebra.CotangentSpace k H) =>
        (Comodule.VectorOrbit.mk (k := k) (H := H) e).image) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        nilpotentConeIdeal k H ≤
          RingHom.ker
            (SymmetricAlgebra.lift
              (Module.Dual.eval k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 := by
  simpa only [nilpotentConeIdeal_le_ker_lift_eval_iff] using
    ncard_image_vectorOrbit_image_mk_setOf_isNilpotent_ad_le (H := H) 𝔥

end SchemeOrbitImages

end TauCeti
