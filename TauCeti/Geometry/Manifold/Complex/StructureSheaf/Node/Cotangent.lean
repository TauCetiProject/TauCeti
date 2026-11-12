/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent

/-!
# The cotangent space of an analytic node

The native cotangent space `𝔪/𝔪²` of the branch-pair node ring has one independent
cotangent direction from each branch. More generally, for two finite-dimensional complex
manifold branches, differentiation in charts identifies it with the product of their complex
dual model spaces. Scalars are compared using evaluation on the node's residue field.

The key local-algebra statement is that a node germ lies in `𝔪²` exactly when both branch
germs lie in their respective squared maximal ideals. Thus there is no first-order relation
between the branches, even though the product of their vanishing germs is zero. This gives
the two cotangent directions used in the local deformation theory of an ordinary node,
without choosing a hypersurface presentation.

The derivative and square-vanishing criterion are supplied by
`OpenPartialHomeomorph.holomorphicStalkFDeriv_eq_zero_iff`. The descent through the native
cotangent quotient and residue-field comparison follows the construction of
`OpenPartialHomeomorph.holomorphicCotangentEquiv`.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open IsLocalRing IsManifold
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf.nodeLocalRing

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {X Y : Type} [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace F Y]
  {p : X} {q : Y}

local notation "N" => nodeLocalRing 𝓘(ℂ, E) 𝓘(ℂ, F) p q
local notation "A" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, E) X)) p
local notation "B" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, F) Y)) q
local notation "π₁" => fst 𝓘(ℂ, E) 𝓘(ℂ, F) p q
local notation "π₂" => snd 𝓘(ℂ, E) 𝓘(ℂ, F) p q

/-- Germs supported on the first branch restrict onto its whole maximal ideal. -/
@[simp]
theorem map_ker_snd : (RingHom.ker π₂).map π₁ = maximalIdeal A := by
  ext a
  rw [Ideal.mem_map_iff_of_surjective _ fst_surjective, maximalIdeal_stalk,
    RingHom.mem_ker]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [eval_fst, ← eval_snd, RingHom.mem_ker.mp hs, map_zero]
  · intro ha
    exact ⟨mk a 0 (by simpa using ha), by simp, by simp⟩

/-- Germs supported on the second branch restrict onto its whole maximal ideal. -/
@[simp]
theorem map_ker_fst : (RingHom.ker π₁).map π₂ = maximalIdeal B := by
  ext b
  rw [Ideal.mem_map_iff_of_surjective _ snd_surjective, maximalIdeal_stalk,
    RingHom.mem_ker]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [eval_snd, ← eval_fst, RingHom.mem_ker.mp hs, map_zero]
  · intro hb
    exact ⟨mk 0 b (by simpa using hb.symm), by simp, by simp⟩

/-- A node germ vanishes to second order exactly when each of its two branch germs does. -/
theorem mem_maximalIdeal_sq_iff (s : N) :
    s ∈ maximalIdeal N ^ 2 ↔
      π₁ s ∈ maximalIdeal A ^ 2 ∧ π₂ s ∈ maximalIdeal B ^ 2 := by
  have h₁ : maximalIdeal N ≤ (maximalIdeal A).comap π₁ := by
    intro t ht
    simpa only [Ideal.mem_comap, maximalIdeal_stalk, RingHom.mem_ker,
      eval_fst, maximalIdeal_eq_ker_eval] using ht
  have h₂ : maximalIdeal N ≤ (maximalIdeal B).comap π₂ := by
    intro t ht
    simpa only [Ideal.mem_comap, maximalIdeal_stalk, RingHom.mem_ker,
      eval_snd, maximalIdeal_eq_ker_eval] using ht
  constructor
  · intro hs
    exact ⟨Ideal.le_comap_pow π₁ 2 (Ideal.pow_right_mono h₁ 2 hs),
      Ideal.le_comap_pow π₂ 2 (Ideal.pow_right_mono h₂ 2 hs)⟩
  · rintro ⟨ha, hb⟩
    -- Lift each branch square to a square supported only on that branch, then add the lifts.
    rw [← map_ker_snd (E := E) (F := F) (p := p) (q := q), ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective _ fst_surjective] at ha
    rw [← map_ker_fst (E := E) (F := F) (p := p) (q := q), ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective _ snd_surjective] at hb
    obtain ⟨u, hu, hua⟩ := ha
    obtain ⟨v, hv, hvb⟩ := hb
    have hu₀ : π₂ u = 0 := RingHom.mem_ker.mp ((Ideal.pow_le_self two_ne_zero) hu)
    have hv₀ : π₁ v = 0 := RingHom.mem_ker.mp ((Ideal.pow_le_self two_ne_zero) hv)
    have hsum : u + v = s := ext (by simp [hua, hv₀]) (by simp [hvb, hu₀])
    rw [← hsum]
    have hk₁ : RingHom.ker π₁ ≤ maximalIdeal N := by
      intro t ht
      rw [maximalIdeal_eq_ker_eval, RingHom.mem_ker, ← eval_fst,
        RingHom.mem_ker.mp ht, map_zero]
    have hk₂ : RingHom.ker π₂ ≤ maximalIdeal N := by
      intro t ht
      rw [maximalIdeal_eq_ker_eval, RingHom.mem_ker, ← eval_snd,
        RingHom.mem_ker.mp ht, map_zero]
    exact Ideal.add_mem _ (Ideal.pow_right_mono hk₂ 2 hu) (Ideal.pow_right_mono hk₁ 2 hv)

variable {e : OpenPartialHomeomorph X E} {e' : OpenPartialHomeomorph Y F}
  (hp : p ∈ e.source) (hq : q ∈ e'.source)
  (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ, F) ω Y)

/-- The derivatives of the two branches of a vanishing node germ. -/
private def maximalIdealFDeriv : maximalIdeal N →ₛₗ[eval 𝓘(ℂ, E) 𝓘(ℂ, F) p q]
    (StrongDual ℂ E × StrongDual ℂ F) where
  toFun s := (e.holomorphicStalkFDeriv p hp (π₁ s),
    e'.holomorphicStalkFDeriv q hq (π₂ s))
  map_add' s t := by
    simp only [Submodule.coe_add, map_add,
      e.holomorphicStalkFDeriv_add p hp he, e'.holomorphicStalkFDeriv_add q hq he']
    rfl
  map_smul' a s := by
    have hs : eval 𝓘(ℂ, E) 𝓘(ℂ, F) p q s = 0 := by
      simpa only [maximalIdeal_eq_ker_eval, RingHom.mem_ker] using s.property
    ext v <;>
      simp [smul_eq_mul, map_mul,
        e.holomorphicStalkFDeriv_mul p hp he,
        e'.holomorphicStalkFDeriv_mul q hq he', hs]

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

include he he' in
private theorem maximalIdealFDeriv_eq_zero_iff (s : maximalIdeal N) :
    maximalIdealFDeriv hp hq he he' s = 0 ↔ (s : N) ∈ maximalIdeal N ^ 2 := by
  have hs₁ : π₁ s ∈ maximalIdeal A := by
    simpa only [maximalIdeal_stalk, RingHom.mem_ker, eval_fst,
      maximalIdeal_eq_ker_eval] using s.property
  have hs₂ : π₂ s ∈ maximalIdeal B := by
    simpa only [maximalIdeal_stalk, RingHom.mem_ker, eval_snd,
      maximalIdeal_eq_ker_eval] using s.property
  rw [mem_maximalIdeal_sq_iff]
  constructor
  · intro h
    exact ⟨(e.holomorphicStalkFDeriv_eq_zero_iff p hp he ⟨π₁ s, hs₁⟩).1
      (congrArg Prod.fst h),
      (e'.holomorphicStalkFDeriv_eq_zero_iff q hq he' ⟨π₂ s, hs₂⟩).1
        (congrArg Prod.snd h)⟩
  · rintro ⟨ha, hb⟩
    exact Prod.ext
      ((e.holomorphicStalkFDeriv_eq_zero_iff p hp he ⟨π₁ s, hs₁⟩).2 ha)
      ((e'.holomorphicStalkFDeriv_eq_zero_iff q hq he' ⟨π₂ s, hs₂⟩).2 hb)

private def cotangentMap : CotangentSpace N →ₛₗ[eval 𝓘(ℂ, E) 𝓘(ℂ, F) p q]
    (StrongDual ℂ E × StrongDual ℂ F) :=
  Submodule.liftQ _ (maximalIdealFDeriv hp hq he he') fun s hs ↦
    (maximalIdealFDeriv_eq_zero_iff hp hq he he' s).2
      ((Ideal.mem_toCotangent_ker _).1 (by
        rw [Ideal.toCotangent, Submodule.ker_mkQ]
        exact hs))

@[simp]
private theorem cotangentMap_toCotangent (s : maximalIdeal N) :
    cotangentMap hp hq he he' (Ideal.toCotangent _ s) =
      (e.holomorphicStalkFDeriv p hp (π₁ s),
        e'.holomorphicStalkFDeriv q hq (π₂ s)) := (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Differentiation identifies the cotangent space of the node ring with the two branch
cotangent model spaces, semilinearly along evaluation on the residue field. -/
def cotangentEquiv :
    LinearEquiv (RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q))
      (σ' := RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q).symm)
      (CotangentSpace N) (StrongDual ℂ E × StrongDual ℂ F) :=
  LinearEquiv.ofBijective
    (σ₂₁ := RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q).symm)
    { toFun := cotangentMap hp hq he he'
      map_add' := map_add _
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := residue_surjective c
        rw [RingHom.coe_coe, residueFieldEquiv_residue,
          ← IsLocalRing.ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul]
        exact (cotangentMap hp hq he he').map_smulₛₗ a v }
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro v hv
      obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
      exact (Ideal.toCotangent_eq_zero _ s).2
        ((maximalIdealFDeriv_eq_zero_iff hp hq he he' s).1 hv),
      fun ℓ ↦ ⟨Ideal.toCotangent _ ⟨mk
        (e.holomorphicLinearCoordinateGerm he p ℓ.1 hp)
        (e'.holomorphicLinearCoordinateGerm he' q ℓ.2 hq) (by simp), by
          simp [maximalIdeal_eq_ker_eval, ← eval_fst]⟩, by
            simp⟩⟩

/-- On a vanishing germ the cotangent comparison is differentiation of its branch germs. -/
@[simp]
theorem cotangentEquiv_toCotangent (s : maximalIdeal N) :
    cotangentEquiv hp hq he he' (Ideal.toCotangent _ s) =
      (e.holomorphicStalkFDeriv p hp (π₁ s),
        e'.holomorphicStalkFDeriv q hq (π₂ s)) := (rfl)

/-- The inverse comparison glues the two centered linear coordinate germs. -/
@[simp]
theorem cotangentEquiv_symm_apply (ℓ : StrongDual ℂ E × StrongDual ℂ F) :
    (cotangentEquiv hp hq he he').symm ℓ = Ideal.toCotangent _ ⟨mk
      (e.holomorphicLinearCoordinateGerm he p ℓ.1 hp)
      (e'.holomorphicLinearCoordinateGerm he' q ℓ.2 hq) (by simp), by
        simp [maximalIdeal_eq_ker_eval, ← eval_fst]⟩ := by
  apply (cotangentEquiv hp hq he he').injective
  simp

include hp hq he he' in
/-- The embedding dimension of the branch-pair ring is the sum of the dimensions of the
branches. In particular, two curve branches give embedding dimension two. -/
theorem finrank_cotangentSpace :
    Module.finrank (ResidueField N) (CotangentSpace N) =
      Module.finrank ℂ E + Module.finrank ℂ F := by
  let c := cotangentEquiv hp hq he he'
  have h := lift_rank_eq_of_equiv_equiv
    (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q) c.toAddEquiv
    (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q).bijective c.map_smulₛₗ
  have hr : Module.finrank (ResidueField N) (CotangentSpace N) =
      Module.finrank ℂ (StrongDual ℂ E × StrongDual ℂ F) := by
    simpa only [Cardinal.toNat_lift, Module.finrank] using congrArg Cardinal.toNat h
  simpa only [Module.finrank_prod, ← LinearMap.toContinuousLinearMap.finrank_eq,
    Subspace.dual_finrank_eq] using hr

section Curves

variable {C D : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ) ω C]
  [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D]

/-- An ordinary analytic node has two independent cotangent directions over its residue field. -/
@[simp]
theorem finrank_cotangentSpace_eq_two (p : C) (q : D) :
    Module.finrank (ResidueField (nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) p q))
      (CotangentSpace (nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) p q)) = 2 := by
  simpa using finrank_cotangentSpace (mem_chart_source ℂ p) (mem_chart_source ℂ q)
    (chart_mem_maximalAtlas p (I := 𝓘(ℂ)) (n := ω))
    (chart_mem_maximalAtlas q (I := 𝓘(ℂ)) (n := ω))

end Curves

end TauCeti.holomorphicStructureSheaf.nodeLocalRing
