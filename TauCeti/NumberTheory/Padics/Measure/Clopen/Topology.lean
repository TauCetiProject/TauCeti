/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Clopen.Basic
public import TauCeti.NumberTheory.Padics.Measure.Pushforward

/-!
# Topologies on clopen measure decompositions

Restriction to a clopen subset and inclusion pushforward are continuous for both the weak
and strong topologies on abstract measures. Inclusion is a closed embedding, and the algebraic
clopen decomposition is a homeomorphism in either topology. For measures with values in a
seminormed module over a field, restriction contracts the continuous-dual operator norm and
inclusion preserves it exactly.

These results allow measures supported on a clopen subset, such as a residue class or the
p-adic units, to be treated intrinsically without changing their topology. Measures may take
values in a normed module. The weak and strong topologies are always selected explicitly;
no global topology or norm instance on measures is introduced.

## References

Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, Definitions 3.5,
3.7–3.8, Remark 3.31 and Corollary 3.32.
-/

public section

open AbstractMeasure ContinuousMap TopologicalSpace Topology

namespace TopologicalSpace.Clopens

variable {X R E : Type*} [TopologicalSpace X] [CompactSpace X]

section Weak

variable [NormedCommRing R] [NormedAddCommGroup E] [Module R E] [ContinuousSMul R E]

/-- Restriction to a clopen subset is continuous for the weak measure topologies. -/
theorem continuous_restrictClopen_weak (s : Clopens X) :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := E))
      (WeakTopology (X := s) (R := R) (E := E)) (restrictClopen s) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  let : TopologicalSpace (AbstractMeasure s R E) := WeakTopology
  have heval : Continuous (fun μ : AbstractMeasure X R E ↦ fun f : C(X, R) ↦ μ f) :=
    continuous_induced_dom
  refine continuous_induced_rng.mpr <| continuous_pi fun f ↦ ?_
  exact ((continuous_apply (zeroExtendClopen R s f)).comp heval).congr fun μ ↦
    (restrictClopen_apply s μ f).symm

/-- Inclusion of measures from a clopen subset is a closed embedding for the weak topologies.
Its image consists of the measures annihilating tests vanishing on that subset, as characterized
by `AbstractMeasure.existsUnique_map_subtype_iff`. -/
theorem isClosedEmbedding_map_subtype_weak (s : Clopens X) :
    @IsClosedEmbedding _ _ (WeakTopology (X := s) (R := R) (E := E))
      (WeakTopology (X := X) (R := R) (E := E)) (map (subtypeVal (s : Set X))) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  let : TopologicalSpace (AbstractMeasure s R E) := WeakTopology
  have heval : Continuous (fun μ : AbstractMeasure X R E ↦ fun f : C(X, R) ↦ μ f) :=
    continuous_induced_dom
  let : T2Space (AbstractMeasure X R E) :=
    T2Space.of_injective_continuous DFunLike.coe_injective heval
  exact Function.LeftInverse.isClosedEmbedding
    (restrictClopen_map_subtype (R := R) (E := E) s)
    (continuous_restrictClopen_weak s) (subtypeVal (s : Set X)).continuous_abstractMeasure_map_weak

/-- The clopen decomposition is a homeomorphism for the weak measure topologies and their
product topology. Its inverse is the sum of the two inclusion pushforwards. -/
theorem isHomeomorph_clopenDecomposition_weak (s : Clopens X) :
    @IsHomeomorph _ _ (WeakTopology (X := X) (R := R) (E := E))
      (@instTopologicalSpaceProd _ _ (WeakTopology (X := s) (R := R) (E := E))
        (WeakTopology (X := ↥sᶜ) (R := R) (E := E))) (clopenDecomposition s) := by
  let : TopologicalSpace (AbstractMeasure X R E) := WeakTopology
  let : TopologicalSpace (AbstractMeasure s R E) := WeakTopology
  let : TopologicalSpace (AbstractMeasure ↥sᶜ R E) := WeakTopology
  rw [LinearEquiv.isHomeomorph_iff]
  constructor
  · exact ((continuous_restrictClopen_weak s).prodMk
      (continuous_restrictClopen_weak sᶜ)).congr fun μ ↦ (clopenDecomposition_apply s μ).symm
  · have heval (t : Clopens X) :
        @Continuous _ _ (WeakTopology (X := t) (R := R) (E := E)) inferInstance
          (fun μ : AbstractMeasure t R E ↦ fun f : C(t, R) ↦ μ f) :=
      continuous_induced_dom
    refine continuous_induced_rng.mpr <| continuous_pi fun f ↦ ?_
    exact (((continuous_apply (f.comp (subtypeVal (s : Set X)))).comp
      ((heval s).comp continuous_fst)).add
      ((continuous_apply (f.comp (subtypeVal ((sᶜ : Clopens X) : Set X)))).comp
        ((heval sᶜ).comp continuous_snd))).congr fun μ ↦ by
          simp only [Pi.add_apply, Function.comp_apply, clopenDecomposition_symm_apply,
            _root_.add_apply, map_apply]

end Weak

section OperatorNorm

variable [NontriviallyNormedField R] [SeminormedAddCommGroup E] [NormedSpace R E]

/-- Clopen restriction does not increase the continuous-dual operator norm. -/
theorem norm_toCLMEquiv_restrictClopen_le (s : Clopens X) (μ : AbstractMeasure X R E) :
    ‖toCLMEquiv (restrictClopen s μ)‖ ≤ ‖toCLMEquiv μ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ ?_
  simpa only [coe_toCLMEquiv, restrictClopen_apply, norm_zeroExtendClopen] using
    (toCLMEquiv μ).le_opNorm (zeroExtendClopen R s f)

/-- Inclusion of measures from a clopen subset preserves the continuous-dual operator norm,
including when the subset is empty. -/
-- Simplify before `toCLMEquiv_map` rewrites the inner pushforward to precomposition.
@[simp↓]
theorem norm_toCLMEquiv_map_subtype (s : Clopens X) (ν : AbstractMeasure s R E) :
    ‖toCLMEquiv (map (subtypeVal (s : Set X)) ν)‖ = ‖toCLMEquiv ν‖ := by
  refine le_antisymm (norm_toCLMEquiv_map_le ν _) ?_
  have h := norm_toCLMEquiv_restrictClopen_le s (map (subtypeVal (s : Set X)) ν)
  rw [restrictClopen_map_subtype (R := R) (E := E)] at h
  exact h

end OperatorNorm

section Strong

variable [NontriviallyNormedField R] [NormedAddCommGroup E] [NormedSpace R E]

/-- Clopen restriction is continuous for the strong continuous-dual topologies. -/
theorem continuous_restrictClopen_strong (s : Clopens X) :
    @Continuous _ _ (StrongTopology (X := X) (R := R) (E := E))
      (StrongTopology (X := s) (R := R) (E := E)) (restrictClopen s) := by
  let : TopologicalSpace (AbstractMeasure X R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure s R E) := StrongTopology
  -- StrongTopology is the continuous-dual topology on the measure type synonym. Precomposition
  -- is continuous in that topology; the evaluation lemmas identify its function with restriction.
  have h := (ContinuousLinearMap.precomp (τ := RingHom.id R) (ρ := RingHom.id R)
    E (zeroExtendClopen R s : C(s, R) →L[R] C(X, R))).continuous
  exact h.congr fun μ ↦ by
    ext f
    exact (restrictClopen_apply s μ f).symm

/-- Inclusion of measures from a clopen subset is a closed embedding for the strong topologies. -/
theorem isClosedEmbedding_map_subtype_strong (s : Clopens X) :
    @IsClosedEmbedding _ _ (StrongTopology (X := s) (R := R) (E := E))
      (StrongTopology (X := X) (R := R) (E := E)) (map (subtypeVal (s : Set X))) := by
  let : TopologicalSpace (AbstractMeasure X R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure s R E) := StrongTopology
  -- The measure synonym with StrongTopology has the Hausdorff continuous-dual topology.
  let : T2Space (AbstractMeasure X R E) := inferInstanceAs (T2Space (C(X, R) →L[R] E))
  exact Function.LeftInverse.isClosedEmbedding
    (restrictClopen_map_subtype (R := R) (E := E) s)
    (continuous_restrictClopen_strong s)
    (subtypeVal (s : Set X)).continuous_abstractMeasure_map_strong

/-- The clopen decomposition is a homeomorphism for the strong measure topologies and their
product topology. No completeness or ultrametricity of the coefficients is required. -/
theorem isHomeomorph_clopenDecomposition_strong (s : Clopens X) :
    @IsHomeomorph _ _ (StrongTopology (X := X) (R := R) (E := E))
      (@instTopologicalSpaceProd _ _ (StrongTopology (X := s) (R := R) (E := E))
        (StrongTopology (X := ↥sᶜ) (R := R) (E := E))) (clopenDecomposition s) := by
  let : TopologicalSpace (AbstractMeasure X R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure s R E) := StrongTopology
  let : TopologicalSpace (AbstractMeasure ↥sᶜ R E) := StrongTopology
  rw [LinearEquiv.isHomeomorph_iff]
  constructor
  · exact ((continuous_restrictClopen_strong s).prodMk
      (continuous_restrictClopen_strong sᶜ)).congr fun μ ↦ (clopenDecomposition_apply s μ).symm
  · -- StrongTopology is the continuous-dual topology, so addition of measures is continuous.
    let : ContinuousAdd (AbstractMeasure X R E) :=
      inferInstanceAs (ContinuousAdd (C(X, R) →L[R] E))
    exact (((subtypeVal (s : Set X)).continuous_abstractMeasure_map_strong.comp continuous_fst).add
      ((subtypeVal ((sᶜ : Clopens X) : Set X)).continuous_abstractMeasure_map_strong.comp
        continuous_snd)).congr fun μ ↦ (clopenDecomposition_symm_apply s μ).symm

end Strong

end TopologicalSpace.Clopens
