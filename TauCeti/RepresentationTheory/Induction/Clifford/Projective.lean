/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic

/-!
# The projective representation of the inertia group on an irreducible of a normal subgroup

Let `N` be a normal subgroup of `G` and let `V : FDRep k N` be simple, over an algebraically
closed field `k`.  By definition an element `g` of the inertia group `TauCeti.inertia V` satisfies
`{}^g V ≅ V`, and such an isomorphism is a linear automorphism `T g` of the *same* space `V` —
conjugation does not move the underlying module — obeying

`T g (ρ (g⁻¹ n g) v) = ρ n (T g v)` for all `n : N`,

where `ρ = V.ρ`.  Schur's lemma makes `T g` unique up to a scalar in `kˣ`
(`TauCeti.exists_units_eq_smul_inertiaTwist`), so a *choice* of `T g` for each `g` — normalized by
`T 1 = 1` — is multiplicative only up to scalars: `T g ∘ T h` and `T (g * h)` both obey the
displayed relation at `g * h`, hence differ by a unit.  Those units are the **factor set**
`TauCeti.inertiaFactorSet V`, and `TauCeti.isProjectiveRep_inertiaTwist` is the statement that
`TauCeti.inertiaTwist V` is a projective representation of `inertia V` on `V` with that factor set,
in the sense of `TauCeti.IsProjectiveRep`.

This is the object behind the Clifford-theory extension obstruction: `V` extends to an ordinary
representation of its inertia group only if this projective representation linearizes, and
`TauCeti.IsProjectiveRep.cohomologyClass` turns the factor set into a Schur-multiplier class.
What is *not* done here is the descent of that class to the quotient `inertia V / N`, where the
roadmap's Clifford obstruction lives; the ingredient this file supplies for it is
`TauCeti.exists_units_inertiaTwist_coe_eq_smul`, which says that on `N` itself the chosen twist
is a scalar multiple of `ρ`, so the projective action of `inertia V` is trivial on `N`.

## Implementation notes

The twist is chosen with `Classical.choice` out of `TauCeti.mem_inertia_iff`, read through
`TauCeti.nonempty_fdRepIso_iff` so that the categorical isomorphism becomes a
`Representation.Equiv` and therefore an honest `V ≃ₗ[k] V`.  Normalization at `1` is forced by
hand, because no choice of isomorphisms can be expected to hit the identity there: the raw choice
at `g` is composed with the inverse of the raw choice at `1`, which is `N`-equivariant because
conjugating by `1` does nothing.  Normalization is load-bearing, since `TauCeti.IsFactorSet` asks
for `α 1 g = α g 1 = 1`.  Neither the choice nor the intertwining relation needs `V` simple, so
the twist and its defining relation are stated for an arbitrary `V`; simplicity enters only with
Schur's lemma.

The intertwining relation is stated with Mathlib's `MulAut.conjNormal`, matching
`TauCeti.conjNormalFDRep_ρ`, and `TauCeti.inertiaTwist_apply_conj_mk` restates it with the
conjugate written in the ambient group.

Once `Nontrivial V` is known — it is, because `V` is simple — the units of `k` act faithfully on
`V`, which is what lets `TauCeti.IsProjectiveRep.of_map_one_mul_apply` derive the cocycle identity
of the factor set from associativity of composition rather than by a direct computation.

## Main definitions

* `TauCeti.inertiaTwist`: the chosen normalized intertwiner `{}^g V ≅ V`, as a linear automorphism
  of `V`, for `g` in the inertia group of `V`.
* `TauCeti.inertiaFactorSet`: the resulting factor set of the inertia group.

## Main statements

* `TauCeti.inertiaTwist_apply_conj` and `TauCeti.inertiaTwist_apply_conj_mk`: the defining
  intertwining relation, in the `MulAut.conjNormal` and ambient-group spellings.
* `TauCeti.exists_units_eq_smul_inertiaTwist`: **Schur uniqueness**, every nonzero map obeying the
  relation at `g` is a unit multiple of `TauCeti.inertiaTwist V g`.
* `TauCeti.inertiaTwist_mul_apply` and `TauCeti.inertiaFactorSet_eq`: the twist is multiplicative
  up to the factor set, and the factor set is the unique family of units for which it is.
* `TauCeti.isProjectiveRep_inertiaTwist`: **the projective representation of the inertia group**,
  with `TauCeti.isFactorSet_inertiaFactorSet` its factor-set axioms.
* `TauCeti.exists_units_inertiaTwist_coe_eq_smul`: on `N` the twist is a scalar multiple of the
  representation itself.

## References

This builds the projective-representation input to the Clifford-theory obstruction of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Chapter 3.

## Tags

Clifford theory, inertia group, projective representation, factor set
-/

public section

open CategoryTheory

namespace TauCeti

universe u

section Schur

variable {k H W : Type*} [Field k] [IsAlgClosed k] [Monoid H] [AddCommGroup W] [Module k W]

/-- Schur's lemma on the underlying module: an endomorphism commuting with an irreducible
finite-dimensional action over an algebraically closed field is a scalar.  This is Mathlib's
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`, read as a
statement about the underlying linear map. -/
private theorem exists_eq_smul_id_of_comm (ρ : Representation k H W) [ρ.IsIrreducible]
    [FiniteDimensional k W] (f : W →ₗ[k] W) (hf : ∀ (h : H) (w : W), f (ρ h w) = ρ h (f w)) :
    ∃ c : k, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (f.intertwiningMap_of_isIntertwiningMap ρ ρ hf)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  simpa using (congrArg (fun q : Representation.IntertwiningMap ρ ρ => q w) hc).symm

end Schur

section Faithful

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

/-- A nonzero vector space carries a faithful scalar action.  This is what makes the factor set
below unique, through the induced `FaithfulSMul kˣ W`. -/
private theorem faithfulSMul_of_nontrivial [Nontrivial W] : FaithfulSMul k W := by
  refine ⟨fun {a b} h => ?_⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hab : (a - b) • w = 0 := by rw [sub_smul, h w, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hab).resolve_right hw)

end Faithful

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [hN : N.Normal] (V : FDRep k N)

/-- An arbitrary choice of isomorphism `{}^g V ≅ V` for `g` in the inertia group, read as a linear
automorphism of `V`.  Conjugation leaves the underlying module alone, so the isomorphism really is
an automorphism of `V`.  This raw choice is unnormalized; `TauCeti.inertiaTwist` corrects it at
`1`. -/
private noncomputable def rawInertiaTwist (g : inertia V) : V ≃ₗ[k] V :=
  (nonempty_fdRepIso_iff.mp (mem_inertia_iff.mp g.2)).some.toLinearEquiv

private theorem rawInertiaTwist_apply_conj (g : inertia V) (n : N) (v : V) :
    rawInertiaTwist V g (V.ρ (MulAut.conjNormal (g : G)⁻¹ n) v)
      = V.ρ n (rawInertiaTwist V g v) :=
  congrFun (congrArg (fun q : V →ₗ[k] V => (q : V → V))
    ((nonempty_fdRepIso_iff.mp (mem_inertia_iff.mp g.2)).some.toIntertwiningMap.2 n)) v

/-- **The chosen intertwiner of `{}^g V` with `V`**, for `g` in the inertia group of
`V : FDRep k N`, normalized to be the identity at `1`.  Conjugation leaves the underlying module
alone, so the isomorphism is a linear automorphism of `V`.  Normalization is arranged by composing
an arbitrary choice with the inverse of the choice made at `1`, which is itself `N`-equivariant.
Once `V` is simple the twist is determined by this choice up to a scalar
(`TauCeti.exists_units_eq_smul_inertiaTwist`). -/
noncomputable def inertiaTwist (g : inertia V) : V ≃ₗ[k] V :=
  (rawInertiaTwist V g).trans (rawInertiaTwist V 1).symm

private theorem inertiaTwist_apply (g : inertia V) (v : V) :
    inertiaTwist V g v = (rawInertiaTwist V 1).symm (rawInertiaTwist V g v) :=
  (rfl)

/-- The twist is normalized: the identity of the inertia group acts as the identity. -/
@[simp]
theorem inertiaTwist_one : inertiaTwist V 1 = LinearEquiv.refl k V :=
  LinearEquiv.ext fun v => by
    rw [inertiaTwist_apply, LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply]

/-- The choice made at `1` is `N`-equivariant, since conjugating by `1` does nothing. -/
private theorem rawInertiaTwist_one_symm_apply (n : N) (v : V) :
    (rawInertiaTwist V 1).symm (V.ρ n v) = V.ρ n ((rawInertiaTwist V 1).symm v) := by
  refine (rawInertiaTwist V 1).injective ?_
  have hone : MulAut.conjNormal (((1 : inertia V) : G))⁻¹ n = n := by simp
  have h := rawInertiaTwist_apply_conj V 1 n ((rawInertiaTwist V 1).symm v)
  rw [hone] at h
  rw [LinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply]

/-- **The defining relation of the twist**: `T g` intertwines the conjugate action `{}^g ρ`
with `ρ`. -/
theorem inertiaTwist_apply_conj (g : inertia V) (n : N) (v : V) :
    inertiaTwist V g (V.ρ (MulAut.conjNormal (g : G)⁻¹ n) v) = V.ρ n (inertiaTwist V g v) := by
  rw [inertiaTwist_apply, inertiaTwist_apply, rawInertiaTwist_apply_conj V g n v,
    rawInertiaTwist_one_symm_apply V n]

/-- The defining relation of the twist, with the conjugate written in the ambient group. -/
theorem inertiaTwist_apply_conj_mk (g : inertia V) (n : N) (v : V) :
    inertiaTwist V g (V.ρ ⟨(g : G)⁻¹ * (n : G) * (g : G),
        hN.conj_mem' (n : G) n.2 (g : G)⟩ v) = V.ρ n (inertiaTwist V g v) := by
  refine Eq.trans (congrArg _ (congrArg (fun m => V.ρ m v) ?_)) (inertiaTwist_apply_conj V g n v)
  exact Subtype.ext (MulAut.conjNormal_inv_apply (g : G) n).symm

variable [IsAlgClosed k] [Simple V]

/-- **Schur uniqueness for the twist.** Any nonzero linear map obeying the intertwining relation at
`g` is a unit multiple of `TauCeti.inertiaTwist V g`; in particular the twist is determined up to a
scalar, which is exactly why the factor set below is well defined only up to a coboundary. -/
theorem exists_units_eq_smul_inertiaTwist (g : inertia V) (f : V →ₗ[k] V) (hf0 : f ≠ 0)
    (hf : ∀ (n : N) (v : V), f (V.ρ (MulAut.conjNormal (g : G)⁻¹ n) v) = V.ρ n (f v)) :
    ∃ c : kˣ, ∀ v : V, f v = (c : k) • inertiaTwist V g v := by
  have := FDRep.isIrreducible_of_simple V
  have hsymm : ∀ (n : N) (v : V), (inertiaTwist V g).symm (V.ρ n v)
      = V.ρ (MulAut.conjNormal (g : G)⁻¹ n) ((inertiaTwist V g).symm v) := fun n v => by
    refine (inertiaTwist V g).injective ?_
    rw [LinearEquiv.apply_symm_apply,
      inertiaTwist_apply_conj V g n ((inertiaTwist V g).symm v),
      LinearEquiv.apply_symm_apply]
  -- `f` composed with the inverse twist commutes with `ρ`, hence is a scalar.
  have hcomm : ∀ (n : N) (v : V),
      (f ∘ₗ ((inertiaTwist V g).symm : V →ₗ[k] V)) (V.ρ n v)
        = V.ρ n ((f ∘ₗ ((inertiaTwist V g).symm : V →ₗ[k] V)) v) := fun n v => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm n v]
    exact hf n ((inertiaTwist V g).symm v)
  obtain ⟨c, hc⟩ :=
    exists_eq_smul_id_of_comm V.ρ (f ∘ₗ ((inertiaTwist V g).symm : V →ₗ[k] V)) hcomm
  have hcv : ∀ v : V, f v = c • inertiaTwist V g v := fun v => by
    have := congrArg (fun q : V →ₗ[k] V => q (inertiaTwist V g v)) hc
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (LinearMap.ext fun v => by simpa using hcv v)
  exact ⟨Units.mk0 c hc0, fun v => by simpa using hcv v⟩

/-- **The twist is multiplicative up to a unit scalar.** Both `T g ∘ T h` and `T (g * h)` obey the
intertwining relation at `g * h`, so Schur's lemma compares them. -/
theorem exists_units_inertiaTwist_mul (g h : inertia V) :
    ∃ c : kˣ, ∀ v : V,
      inertiaTwist V g (inertiaTwist V h v) = (c : k) • inertiaTwist V (g * h) v := by
  have hnt : Nontrivial V :=
    Representation.IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple V)
  have hne : ((inertiaTwist V g : V →ₗ[k] V)) ∘ₗ ((inertiaTwist V h : V →ₗ[k] V)) ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hz := LinearMap.ext_iff.mp hzero v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.zero_apply] at hz
    exact hv ((inertiaTwist V h).map_eq_zero_iff.mp ((inertiaTwist V g).map_eq_zero_iff.mp hz))
  have hconj : ∀ (n : N) (v : V),
      (((inertiaTwist V g : V →ₗ[k] V)) ∘ₗ ((inertiaTwist V h : V →ₗ[k] V)))
          (V.ρ (MulAut.conjNormal ((g * h : inertia V) : G)⁻¹ n) v)
        = V.ρ n ((((inertiaTwist V g : V →ₗ[k] V)) ∘ₗ
          ((inertiaTwist V h : V →ₗ[k] V))) v) := fun n v => by
    have key : MulAut.conjNormal ((g * h : inertia V) : G)⁻¹ n
        = MulAut.conjNormal ((h : G))⁻¹ (MulAut.conjNormal ((g : G))⁻¹ n) := by
      have hinv : ((g * h : inertia V) : G)⁻¹ = ((h : G))⁻¹ * ((g : G))⁻¹ := by
        rw [Subgroup.coe_mul, mul_inv_rev]
      rw [hinv, map_mul]
      rfl
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key]
    rw [inertiaTwist_apply_conj V h (MulAut.conjNormal ((g : G))⁻¹ n) v,
      inertiaTwist_apply_conj V g n (inertiaTwist V h v)]
  obtain ⟨c, hc⟩ := exists_units_eq_smul_inertiaTwist V (g * h)
    (((inertiaTwist V g : V →ₗ[k] V)) ∘ₗ ((inertiaTwist V h : V →ₗ[k] V))) hne hconj
  exact ⟨c, fun v => by simpa using hc v⟩

/-- **The factor set of the inertia group**: the unit by which `T g ∘ T h` differs from
`T (g * h)`. -/
noncomputable def inertiaFactorSet (g h : inertia V) : kˣ :=
  (exists_units_inertiaTwist_mul V g h).choose

/-- The defining property of `TauCeti.inertiaFactorSet`. -/
theorem inertiaTwist_mul_apply (g h : inertia V) (v : V) :
    inertiaTwist V g (inertiaTwist V h v)
      = (inertiaFactorSet V g h : k) • inertiaTwist V (g * h) v :=
  (exists_units_inertiaTwist_mul V g h).choose_spec v

/-- **The factor set is determined by the twist**: any unit for which the twist is multiplicative
at `(g, h)` is `TauCeti.inertiaFactorSet V g h`.  So the arbitrary choice in
`TauCeti.inertiaFactorSet` is only the choice of the twists themselves. -/
theorem inertiaFactorSet_eq (g h : inertia V) (c : kˣ)
    (hc : ∀ v : V, inertiaTwist V g (inertiaTwist V h v) = (c : k) • inertiaTwist V (g * h) v) :
    c = inertiaFactorSet V g h := by
  have hnt : Nontrivial V :=
    Representation.IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple V)
  have : FaithfulSMul k V := faithfulSMul_of_nontrivial
  refine FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_
  obtain ⟨w, rfl⟩ := (inertiaTwist V (g * h)).surjective v
  have hw := (hc w).symm.trans (inertiaTwist_mul_apply V g h w)
  simpa [Units.smul_def] using hw

/-- **The inertia group acts projectively on `V`.** The normalized twists form a projective
representation of `inertia V` with factor set `TauCeti.inertiaFactorSet V`; this is the projective
action Clifford theory attaches to an irreducible of a normal subgroup. -/
theorem isProjectiveRep_inertiaTwist :
    IsProjectiveRep (inertiaTwist V) (inertiaFactorSet V) := by
  have hnt : Nontrivial V :=
    Representation.IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple V)
  have : FaithfulSMul k V := faithfulSMul_of_nontrivial
  exact IsProjectiveRep.of_map_one_mul_apply (by rw [inertiaTwist_one]; rfl)
    (inertiaTwist_mul_apply V)

/-- The scalars comparing the twists are a normalized multiplicative `2`-cocycle. -/
theorem isFactorSet_inertiaFactorSet : IsFactorSet (inertiaFactorSet V) :=
  (isProjectiveRep_inertiaTwist V).isFactorSet

/-- **On the normal subgroup the twist is the representation itself, up to a scalar.** The
conjugation by an element of `N` is inner, so `ρ n` already obeys the intertwining relation there,
and Schur's lemma compares it with the chosen twist.  This is why the projective action of the
inertia group is trivial on `N`, and hence the reason the obstruction class is expected to live on
the quotient `inertia V / N`. -/
theorem exists_units_inertiaTwist_coe_eq_smul (n : N) :
    ∃ c : kˣ, ∀ v : V,
      inertiaTwist V ⟨(n : G), le_inertia V n.2⟩ v = (c : k) • V.ρ n v := by
  have hnt : Nontrivial V :=
    Representation.IsIrreducible.nontrivial (FDRep.isIrreducible_of_simple V)
  have hne : V.ρ n ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hz := Representation.self_inv_apply V.ρ n v
    rw [hzero] at hz
    exact hv hz.symm
  have hconj : ∀ (m : N) (v : V),
      V.ρ n (V.ρ (MulAut.conjNormal ((⟨(n : G), le_inertia V n.2⟩ : inertia V) : G)⁻¹ m) v)
        = V.ρ m (V.ρ n v) := fun m v => by
    have key : n * (MulAut.conjNormal ((n : G))⁻¹ m) = m * n := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, MulAut.conjNormal_apply, inv_inv]
      group
    rw [← Module.End.mul_apply, ← map_mul, key, map_mul, Module.End.mul_apply]
  obtain ⟨c, hc⟩ :=
    exists_units_eq_smul_inertiaTwist V ⟨(n : G), le_inertia V n.2⟩ (V.ρ n) hne hconj
  refine ⟨c⁻¹, fun v => ?_⟩
  rw [hc v, smul_smul]
  simp

end TauCeti
