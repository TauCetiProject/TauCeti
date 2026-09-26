/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# Exactness of discrete coinduction

Coinduction from a closed subgroup of a profinite group takes a short exact sequence of
discrete modules to a short exact sequence. This packages the injectivity, middle exactness,
and surjectivity of `TauCeti.coindMap` in the coefficient format used by continuous cohomology.
The surjectivity uses the continuous section of the coset quotient. This is the exact coefficient
sequence used in the coinduced proof of Shapiro's lemma (Ribes–Zalesskii, *Profinite Groups*,
Theorem 6.10.5).
-/

public section

namespace TauCeti.ContCohomology.DiscreteShortExact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (U : Subgroup G)
  (hU : IsClosed (U : Set G))
  {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction U B]
  [ContinuousSMul U B]
  [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction U C]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [ContinuousSMul U B] in
private theorem mapIncl_apply (S : DiscreteShortExact U A B C)
    (a : DiscreteCoind G U A) (g : G) :
    (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a) g = S.incl (a g) := by
  simpa only [AddMonoidHom.coe_toIntLinearMap] using
    (DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant a g)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [ContinuousSMul U B] in
private theorem mapProj_apply (S : DiscreteShortExact U A B C)
    (b : DiscreteCoind G U B) (g : G) :
    (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant b) g = S.proj (b g) := by
  simpa only [AddMonoidHom.coe_toIntLinearMap] using
    (DiscreteCoind.map_apply S.proj.toIntLinearMap S.proj_equivariant b g)

/-- The short exact sequence obtained by applying discrete coinduction from a closed subgroup
to each term and map of a short exact sequence. -/
noncomputable def coind (S : DiscreteShortExact U A B C) :
    DiscreteShortExact G (DiscreteCoind G U A) (DiscreteCoind G U B)
      (DiscreteCoind G U C) where
  incl := (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant).toAddMonoidHom
  proj := (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant).toAddMonoidHom
  incl_equivariant g a := by
    apply DiscreteCoind.ext
    intro x
    -- The short exact sequence stores the linear map as an additive homomorphism.
    change (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant (g • a)) x =
      (g • DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a) x
    calc
      _ = S.incl ((g • a) x) := mapIncl_apply U S _ _
      _ = S.incl (a (x * g)) := by rw [DiscreteCoind.coe_smul]
      _ = (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a) (x * g) :=
        (mapIncl_apply U S _ _).symm
      _ = _ := (DiscreteCoind.coe_smul g _ x).symm
  proj_equivariant g b := by
    apply DiscreteCoind.ext
    intro x
    change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant (g • b)) x =
      (g • DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant b) x
    calc
      _ = S.proj ((g • b) x) := mapProj_apply U S _ _
      _ = S.proj (b (x * g)) := by rw [DiscreteCoind.coe_smul]
      _ = (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant b) (x * g) :=
        (mapProj_apply U S _ _).symm
      _ = _ := (DiscreteCoind.coe_smul g _ x).symm
  incl_injective := by
    intro a b hab
    apply DiscreteCoind.ext
    intro g
    apply S.incl_injective
    have hab' : DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a =
        DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant b := hab
    simpa only [mapIncl_apply] using
      congrArg (fun f : DiscreteCoind G U B => f g) hab'
  proj_surjective := by
    intro c
    obtain ⟨b, hb⟩ := coindMap_surjective hU S.proj S.proj_equivariant
      S.proj_surjective (DiscreteCoind.toCoind G U C c)
    refine ⟨(DiscreteCoind.toCoind G U B).symm b, ?_⟩
    apply DiscreteCoind.ext
    intro g
    change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant
      ((DiscreteCoind.toCoind G U B).symm b)) g = c g
    simpa only [mapProj_apply, coindMap_apply, DiscreteCoind.coe_toCoind_symm,
      DiscreteCoind.coe_toCoind] using
      congrArg (fun f : TauCeti.coind G U C => (f : G → C) g) hb
  exact := by
    have hS : S.incl.range = S.proj.ker := by
      ext b
      exact (S.exact b).symm
    have hcoind := coindMap_range_eq_ker S.incl S.incl_equivariant
      S.proj S.proj_equivariant S.incl_injective hS
    intro b
    constructor
    · intro hb
      have hker : DiscreteCoind.toCoind G U B b ∈
          (coindMap G U S.proj S.proj_equivariant).ker := by
        apply AddMonoidHom.mem_ker.mpr
        apply Subtype.ext
        funext g
        have hb' : DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant b = 0 := hb
        have hg := congrArg (fun f : DiscreteCoind G U C => f g) hb'
        have hg' : S.proj (b g) = 0 := by
          simpa only [mapProj_apply, DiscreteCoind.coe_zero, Pi.zero_apply] using hg
        simpa [coindMap_apply] using hg'
      rw [← hcoind] at hker
      obtain ⟨a, ha⟩ := hker
      refine ⟨(DiscreteCoind.toCoind G U A).symm a, ?_⟩
      apply DiscreteCoind.ext
      intro g
      change (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant
        ((DiscreteCoind.toCoind G U A).symm a)) g = b g
      simpa only [mapIncl_apply, coindMap_apply, DiscreteCoind.coe_toCoind_symm,
        DiscreteCoind.coe_toCoind] using
        congrArg (fun f : TauCeti.coind G U B => (f : G → B) g) ha
    · rintro ⟨a, rfl⟩
      apply DiscreteCoind.ext
      intro g
      change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant
        (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a)) g = 0
      simpa only [mapProj_apply, mapIncl_apply] using S.proj_incl (a g)

/-- Coinduction applies the inclusion of a short exact sequence pointwise. -/
@[simp]
theorem coind_incl_apply (S : DiscreteShortExact U A B C)
    (a : DiscreteCoind G U A) (g : G) :
    (coind U hU S).incl a g = S.incl (a g) :=
  mapIncl_apply U S a g

/-- Coinduction applies the projection of a short exact sequence pointwise. -/
@[simp]
theorem coind_proj_apply (S : DiscreteShortExact U A B C)
    (b : DiscreteCoind G U B) (g : G) :
    (coind U hU S).proj b g = S.proj (b g) :=
  mapProj_apply U S b g

end TauCeti.ContCohomology.DiscreteShortExact
