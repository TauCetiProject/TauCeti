/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Splittings and nonabelian first cohomology

Fix a splitting `s` of a group extension with kernel `N` and quotient `G`. Conjugation
by `s` makes `N` a `G`-group. Every other splitting is uniquely of the form
`g ↦ S.inl (f g) * s g`, where `f` is a nonabelian `1`-cocycle. Kernel conjugacy of
splittings corresponds exactly to cohomology of these cocycles.

The equivalences below use the existing `TauCeti.NonabelianH1` and its cocycles.
The quotient group has the discrete topology, so continuity imposes no restriction;
the topology on the kernel is arbitrary. The action is supplied explicitly with its
agreement with conjugation by the reference splitting. No commutativity of the kernel
is assumed, and the reference splitting is essential: a general nonsplit extension
does not provide an action of the quotient on its kernel.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker, 1985.
-/

public section

namespace GroupExtension.Splitting

open TauCeti TauCeti.GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]
  {S : GroupExtension N E G}

variable [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace N]
  [MulDistribMulAction G N] (s : S.Splitting)
  (hact : ∀ g n, g • n = S.conjAct (s g) n)

/-- The cocycle measuring another splitting relative to `s`. -/
noncomputable def toCocycle (t : S.Splitting) : NonabelianH1.Cocycle G N where
  toFun := sectionDiff t.toSection s.toSection
  continuous_toFun := continuous_of_discreteTopology
  map_mul' g h := by
    apply S.inl_injective
    simp only [inl_sectionDiff, toSection_apply, map_mul, s.inl_smul hact]
    group

/-- The difference cocycle is characterized by the two splittings in the middle group. -/
@[simp]
theorem inl_toCocycle (t : S.Splitting) (g : G) :
    S.inl (s.toCocycle hact t g) = t g * (s g)⁻¹ :=
  inl_sectionDiff t.toSection s.toSection g

/-- A cocycle changes the reference splitting by left multiplication in the kernel. -/
def ofCocycle (f : NonabelianH1.Cocycle G N) : S.Splitting where
  toFun g := S.inl (f g) * s g
  map_one' := by simp
  map_mul' g h := by
    rw [f.apply_mul, map_mul, s.inl_smul hact, map_mul]
    group
  rightInverse_rightHom g := by simp

omit [DiscreteTopology G] in
@[simp]
theorem ofCocycle_apply (f : NonabelianH1.Cocycle G N) (g : G) :
    s.ofCocycle hact f g = S.inl (f g) * s g := (rfl)

omit [DiscreteTopology G] in
/-- The trivial cocycle preserves the reference splitting. -/
@[simp]
theorem ofCocycle_one : s.ofCocycle hact 1 = s := by
  apply DFunLike.ext
  intro g
  simp

@[simp]
theorem toCocycle_ofCocycle (f : NonabelianH1.Cocycle G N) :
    s.toCocycle hact (s.ofCocycle hact f) = f := by
  ext g
  apply S.inl_injective
  simp

@[simp]
theorem ofCocycle_toCocycle (t : S.Splitting) :
    s.ofCocycle hact (s.toCocycle hact t) = t := by
  apply DFunLike.ext
  intro g
  simp

/-- Splittings are bijective with nonabelian cocycles for the action induced by `s`. -/
noncomputable def cocycleEquiv : S.Splitting ≃ NonabelianH1.Cocycle G N where
  toFun := s.toCocycle hact
  invFun := s.ofCocycle hact
  left_inv := s.ofCocycle_toCocycle hact
  right_inv := s.toCocycle_ofCocycle hact

@[simp]
theorem cocycleEquiv_apply (t : S.Splitting) :
    s.cocycleEquiv hact t = s.toCocycle hact t := (rfl)

@[simp]
theorem cocycleEquiv_symm_apply (f : NonabelianH1.Cocycle G N) :
    (s.cocycleEquiv hact).symm f = s.ofCocycle hact f := (rfl)

/-- The reference splitting corresponds to the trivial cocycle. -/
@[simp]
theorem toCocycle_self : s.toCocycle hact s = 1 := by
  ext g
  apply S.inl_injective
  simp

/-- Cohomology of difference cocycles is exactly kernel conjugacy of splittings. -/
theorem toCocycle_equiv_iff (t u : S.Splitting) :
    s.toCocycle hact t ≈ s.toCocycle hact u ↔ S.IsConj t u := by
  rw [NonabelianH1.Cocycle.equiv_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, funext fun g => ?_⟩
    have h := congrArg S.inl (ha g)
    simp only [inl_toCocycle, map_mul, map_inv, s.inl_smul hact] at h
    have h' := congrArg (fun x : E => S.inl a * x * s g * (S.inl a)⁻¹) h
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel, mul_one] using h'.symm
  · rintro ⟨a, ha⟩
    refine ⟨a, fun g => S.inl_injective ?_⟩
    simp only [inl_toCocycle, map_mul, map_inv, s.inl_smul hact]
    rw [congrFun ha g]
    group

/-- Kernel-conjugacy classes of splittings are classified by nonabelian `H¹` for the
specified reference splitting. This equivalence does not assert a group structure on `H¹`. -/
noncomputable def nonabelianH1Equiv : S.ConjClasses ≃ NonabelianH1 G N :=
  Equiv.ofBijective
    (Quotient.lift (fun t => NonabelianH1.mk (s.toCocycle hact t))
      (fun t u h => NonabelianH1.mk_eq_mk_iff.mpr
        (NonabelianH1.Cocycle.equiv_iff.mp ((s.toCocycle_equiv_iff hact t u).mpr h)))) (by
        constructor
        · intro x y
          refine Quotient.inductionOn₂ x y fun t u h => ?_
          apply Quotient.sound
          exact (s.toCocycle_equiv_iff hact t u).mp
            (NonabelianH1.Cocycle.equiv_iff.mpr (NonabelianH1.mk_eq_mk_iff.mp h))
        · intro x
          obtain ⟨f, rfl⟩ := NonabelianH1.mk_surjective x
          exact ⟨Quotient.mk _ (s.ofCocycle hact f), by simp⟩)

@[simp]
theorem nonabelianH1Equiv_mk (t : S.Splitting) :
    s.nonabelianH1Equiv hact (Quotient.mk _ t) = NonabelianH1.mk (s.toCocycle hact t) := (rfl)

/-- The inverse classification recovers the splitting associated to a representing cocycle. -/
@[simp]
theorem nonabelianH1Equiv_symm_mk (f : NonabelianH1.Cocycle G N) :
    (s.nonabelianH1Equiv hact).symm (NonabelianH1.mk f) =
      Quotient.mk _ (s.ofCocycle hact f) := by
  apply (s.nonabelianH1Equiv hact).injective
  simp

end GroupExtension.Splitting
