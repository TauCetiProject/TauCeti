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
This is the exact coefficient sequence used in the coinduced proof of Shapiro's lemma
(Ribes–Zalesskii, *Profinite Groups*, Theorem 6.10.5).
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

/-- The short exact sequence obtained by applying discrete coinduction from a closed subgroup
to each term and map of a short exact sequence. -/
noncomputable def coind (S : DiscreteShortExact U A B C) :
    DiscreteShortExact G (DiscreteCoind G U A) (DiscreteCoind G U B)
      (DiscreteCoind G U C) where
  incl := (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant).toAddMonoidHom
  proj := (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant).toAddMonoidHom
  incl_equivariant g a :=
    DiscreteCoind.map_smul S.incl.toIntLinearMap S.incl_equivariant g a
  proj_equivariant g b :=
    DiscreteCoind.map_smul S.proj.toIntLinearMap S.proj_equivariant g b
  incl_injective := by
    intro a b hab
    apply DiscreteCoind.ext
    intro g
    apply S.incl_injective
    have hab' : DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a =
        DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant b := hab
    have ha := DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant a g
    have hb := DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant b g
    simpa only [ha, hb, AddMonoidHom.coe_toIntLinearMap] using
      congrArg (fun f : DiscreteCoind G U B => f g) hab'
  proj_surjective := by
    intro c
    obtain ⟨b, hb⟩ := coindMap_surjective hU S.proj S.proj_equivariant
      S.proj_surjective (DiscreteCoind.toCoind G U C c)
    refine ⟨(DiscreteCoind.toCoind G U B).symm b, ?_⟩
    apply DiscreteCoind.ext
    intro g
    -- Unfold the projection field to compare it pointwise with `coindMap` via `hb`.
    change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant
      ((DiscreteCoind.toCoind G U B).symm b)) g = c g
    rw [DiscreteCoind.map_apply S.proj.toIntLinearMap S.proj_equivariant]
    simpa only [AddMonoidHom.coe_toIntLinearMap, coindMap_apply, DiscreteCoind.coe_toCoind_symm,
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
          rw [DiscreteCoind.map_apply S.proj.toIntLinearMap S.proj_equivariant] at hg
          simpa only [AddMonoidHom.coe_toIntLinearMap,
            DiscreteCoind.coe_zero, Pi.zero_apply] using hg
        simpa [coindMap_apply] using hg'
      rw [← hcoind] at hker
      obtain ⟨a, ha⟩ := hker
      refine ⟨(DiscreteCoind.toCoind G U A).symm a, ?_⟩
      apply DiscreteCoind.ext
      intro g
      -- Unfold the inclusion field to compare it pointwise with `coindMap` via `ha`.
      change (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant
        ((DiscreteCoind.toCoind G U A).symm a)) g = b g
      rw [DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant]
      simpa only [AddMonoidHom.coe_toIntLinearMap, coindMap_apply,
        DiscreteCoind.coe_toCoind_symm,
        DiscreteCoind.coe_toCoind] using
        congrArg (fun f : TauCeti.coind G U B => (f : G → B) g) ha
    · rintro ⟨a, rfl⟩
      apply DiscreteCoind.ext
      intro g
      -- Expose both map fields so their pointwise composition is `S.proj_incl`.
      change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant
        (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a)) g = 0
      rw [DiscreteCoind.map_apply S.proj.toIntLinearMap S.proj_equivariant,
        DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant]
      simpa only [AddMonoidHom.coe_toIntLinearMap] using S.proj_incl (a g)

/-- Coinduction applies the inclusion of a short exact sequence pointwise. -/
@[simp]
theorem coind_incl_apply (S : DiscreteShortExact U A B C)
    (a : DiscreteCoind G U A) (g : G) :
    (coind U hU S).incl a g = S.incl (a g) :=
  by
    -- The inclusion field forgets the linear structure of `DiscreteCoind.map`.
    change (DiscreteCoind.map S.incl.toIntLinearMap S.incl_equivariant a) g = S.incl (a g)
    simpa only [AddMonoidHom.coe_toIntLinearMap] using
      (DiscreteCoind.map_apply S.incl.toIntLinearMap S.incl_equivariant a g)

/-- Coinduction applies the projection of a short exact sequence pointwise. -/
@[simp]
theorem coind_proj_apply (S : DiscreteShortExact U A B C)
    (b : DiscreteCoind G U B) (g : G) :
    (coind U hU S).proj b g = S.proj (b g) :=
  by
    -- The projection field forgets the linear structure of `DiscreteCoind.map`.
    change (DiscreteCoind.map S.proj.toIntLinearMap S.proj_equivariant b) g = S.proj (b g)
    simpa only [AddMonoidHom.coe_toIntLinearMap] using
      (DiscreteCoind.map_apply S.proj.toIntLinearMap S.proj_equivariant b g)

end TauCeti.ContCohomology.DiscreteShortExact
