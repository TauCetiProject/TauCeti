/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Changing the period map of a Novikov ring

An additive equivalence of exponent groups which rescales periods by a positive constant
induces an algebra equivalence of Novikov rings. Its coefficient formula and exact transport
of the period filtration show that it is a homeomorphism for the period topologies.

In particular, positive rescaling of the period map preserves every coefficient, whereas
reversing the period map transports the coefficient at `h` to `-h`. The latter comparison
reverses the direction of completion; it does not identify the two coefficient functions.
These comparisons allow changes of potential scale and deck-group conventions without
changing completed chain coefficients.

The construction uses the pushforward and restriction of
`TauCeti.RingTheory.NovikovSeries.Map` and their multiplicativity from
`TauCeti.RingTheory.NovikovSeries.Functoriality`.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H H' : Type*}

section Reindex

variable [AddGroup H] [AddMonoid H'] {N : H →+ ℝ} {N' : H' →+ ℝ}

section Algebra

variable [CommSemiring R] (e : H ≃+ H')
  (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)

/-- Reindex Novikov series by an additive equivalence rescaling periods positively.
The inverse is coefficient restriction along the same equivalence. -/
def reindexAlgEquiv : NovikovSeries R H N ≃ₐ[R] NovikovSeries R H' N' where
  __ := mapAlgHom (AlgHom.id R R) (e : H →+ H') he
  toFun := mapAlgHom (AlgHom.id R R) (e : H →+ H') he
  invFun := comap (e : H →+ H') he (by
    rw [(e : H →+ H').ker_eq_bot e.injective]
    exact Set.finite_singleton 0)
  left_inv a := by
    ext h
    simp only [mapAlgHom_apply, coeff_comap]
    exact coeff_map_of_injective (AddMonoidHom.id R) (e : H →+ H') he e.injective _ _
  right_inv b := by
    ext h'
    obtain ⟨h, rfl⟩ := e.surjective h'
    simp only [mapAlgHom_apply]
    exact (coeff_map_of_injective ((AlgHom.id R R : R →+* R) : R →+ R)
      (e : H →+ H') he e.injective _ h).trans (coeff_comap (e : H →+ H') he _ b h)

theorem reindexAlgEquiv_apply (a : NovikovSeries R H N) :
    reindexAlgEquiv e he a = map (AddMonoidHom.id R) (e : H →+ H') he a :=
  mapAlgHom_apply (AlgHom.id R R) (e : H →+ H') he a

/-- Reindexing moves the coefficient at `h` to `e h`. -/
@[simp]
theorem coeff_reindexAlgEquiv (a : NovikovSeries R H N) (h' : H') :
    (reindexAlgEquiv e he a).coeff h' = a.coeff (e.symm h') := by
  obtain ⟨h, rfl⟩ := e.surjective h'
  rw [reindexAlgEquiv_apply]
  simpa using coeff_map_of_injective (AddMonoidHom.id R) (e : H →+ H') he e.injective a h

/-- The inverse comparison restricts coefficients along `e`. -/
@[simp]
theorem coeff_reindexAlgEquiv_symm (b : NovikovSeries R H' N') (h : H) :
    ((reindexAlgEquiv e he).symm b).coeff h = b.coeff (e h) :=
  coeff_comap (e : H →+ H') he _ b h

/-- Reindexing carries monomials to monomials with the corresponding exponent. -/
@[simp]
theorem reindexAlgEquiv_single (h : H) (r : R) :
    reindexAlgEquiv e he (single h r) = single (e h) r := by
  rw [reindexAlgEquiv_apply, map_single]
  rfl

end Algebra

section Topology

variable [CommRing R] (e : H ≃+ H')
  (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)

/-- Reindexing identifies the period neighbourhood at `C` with that at `c * C`. -/
theorem reindexAlgEquiv_mem_periodFiltration_iff {c C : ℝ} (hc : 0 < c)
    (hcN : ∀ h, N' (e h) = c * N h) (a : NovikovSeries R H N) :
    reindexAlgEquiv e he a ∈ periodFiltration R N' (c * C) ↔
      a ∈ periodFiltration R N C := by
  simp only [mem_periodFiltration, coeff_reindexAlgEquiv]
  constructor
  · intro ha h hh
    simpa using ha (e h) (by rw [hcN]; exact mul_lt_mul_of_pos_left hh hc)
  · intro ha h' hh'
    obtain ⟨h, rfl⟩ := e.surjective h'
    rw [hcN, mul_lt_mul_iff_right₀ hc] at hh'
    simpa using ha h hh'

/-- Positive period-rescaling reindexings are isomorphisms of topological algebras. -/
def reindexContinuousAlgEquiv : NovikovSeries R H N ≃A[R] NovikovSeries R H' N' where
  __ := reindexAlgEquiv e he
  toFun := reindexAlgEquiv e he
  continuous_toFun :=
    (continuous_map (AddMonoidHom.id R) (e : H →+ H') he).congr
      fun a => (reindexAlgEquiv_apply e he a).symm
  continuous_invFun := by
    refine continuous_of_continuousAt_zero (reindexAlgEquiv e he).symm.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    obtain ⟨c, hc, hcN⟩ := he
    refine (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨c * C, trivial, fun b hb => ?_⟩
    exact (reindexAlgEquiv_mem_periodFiltration_iff e ⟨c, hc, hcN⟩ hc hcN _).1
      (by simpa using hb)

@[simp]
theorem reindexContinuousAlgEquiv_apply (a : NovikovSeries R H N) :
    reindexContinuousAlgEquiv e he a = reindexAlgEquiv e he a :=
  (rfl)

@[simp]
theorem reindexContinuousAlgEquiv_symm_apply (b : NovikovSeries R H' N') :
    (reindexContinuousAlgEquiv e he).symm b = (reindexAlgEquiv e he).symm b :=
  (rfl)

end Topology

end Reindex

section Rescale

variable [AddGroup H] [CommRing R] (N : H →+ ℝ) {c : ℝ} (hc : 0 < c)

/-- Positive rescaling of the period map gives the same completed algebra and topology,
by the coefficient-preserving comparison. -/
def rescaleContinuousAlgEquiv : NovikovSeries R H N ≃A[R] NovikovSeries R H (c • N) :=
  reindexContinuousAlgEquiv (AddEquiv.refl H) ⟨c, hc, fun _ => rfl⟩

@[simp]
theorem coeff_rescaleContinuousAlgEquiv (a : NovikovSeries R H N) (h : H) :
    (rescaleContinuousAlgEquiv N hc a).coeff h = a.coeff h := by
  simp [rescaleContinuousAlgEquiv]

@[simp]
theorem coeff_rescaleContinuousAlgEquiv_symm (a : NovikovSeries R H (c • N)) (h : H) :
    ((rescaleContinuousAlgEquiv N hc).symm a).coeff h = a.coeff h := by
  simp [rescaleContinuousAlgEquiv]

/-- Positive rescaling fixes every monomial. -/
@[simp]
theorem rescaleContinuousAlgEquiv_single (h : H) (r : R) :
    rescaleContinuousAlgEquiv N hc (single h r) = single h r := by
  simp [rescaleContinuousAlgEquiv]

/-- Under positive rescaling, the cutoff `C` becomes `c * C`. -/
theorem rescaleContinuousAlgEquiv_mem_periodFiltration_iff (C : ℝ)
    (a : NovikovSeries R H N) :
    rescaleContinuousAlgEquiv N hc a ∈ periodFiltration R (c • N) (c * C) ↔
      a ∈ periodFiltration R N C :=
  reindexAlgEquiv_mem_periodFiltration_iff (AddEquiv.refl H) _ hc (fun _ => rfl) a

end Rescale

section Reverse

variable [AddCommGroup H] [CommRing R] (N : H →+ ℝ)

/-- Reversing periods gives a topological algebra isomorphism by negating exponents.
In particular, this map sends `e^h` to `e^(-h)`. -/
def reverseContinuousAlgEquiv : NovikovSeries R H N ≃A[R] NovikovSeries R H (-N) :=
  reindexContinuousAlgEquiv (AddEquiv.neg H) ⟨1, one_pos, by simp⟩

@[simp]
theorem coeff_reverseContinuousAlgEquiv (a : NovikovSeries R H N) (h : H) :
    (reverseContinuousAlgEquiv N a).coeff h = a.coeff (-h) := by
  simp [reverseContinuousAlgEquiv]

@[simp]
theorem coeff_reverseContinuousAlgEquiv_symm (a : NovikovSeries R H (-N)) (h : H) :
    ((reverseContinuousAlgEquiv N).symm a).coeff h = a.coeff (-h) := by
  simp [reverseContinuousAlgEquiv]

/-- Period reversal negates the exponent of every monomial. -/
@[simp]
theorem reverseContinuousAlgEquiv_single (h : H) (r : R) :
    reverseContinuousAlgEquiv N (single h r) = single (-h) r := by
  simp [reverseContinuousAlgEquiv]

/-- Period reversal preserves cutoffs when accompanied by exponent negation. -/
theorem reverseContinuousAlgEquiv_mem_periodFiltration_iff (C : ℝ)
    (a : NovikovSeries R H N) :
    reverseContinuousAlgEquiv N a ∈ periodFiltration R (-N) C ↔
      a ∈ periodFiltration R N C := by
  simpa only [reverseContinuousAlgEquiv, reindexContinuousAlgEquiv_apply, one_mul] using
    reindexAlgEquiv_mem_periodFiltration_iff (AddEquiv.neg H)
      (N' := -N) ⟨1, one_pos, by simp⟩ one_pos (by simp) (C := C) a

end Reverse

end TauCeti.NovikovSeries
