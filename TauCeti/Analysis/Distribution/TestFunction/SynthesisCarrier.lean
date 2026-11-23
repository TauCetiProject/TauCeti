/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Frechet
public import TauCeti.Analysis.Distribution.TestFunction.Separable
public import TauCeti.Analysis.LocallyConvex.WeightedSynthesis

/-!
# A separable Banach space of functions supported in a compact set

Transversality arguments perturb geometric data (Hamiltonian terms, almost complex structures)
along a separable Banach space of smooth directions, so that the Sard–Smale theorem applies while
every perturbation stays smooth. This file constructs such a space for the `C^n` functions
supported in a fixed compact set `K`, `n = ∞` included, with values in a separable Banach space.

The space `𝓓^{n}_{K}(E, F)` is a separable Fréchet space
(`ContDiffMapSupportedIn.instCompleteSpace`, `ContDiffMapSupportedIn.instSecondCountableTopology`),
so it has a dense sequence `e ν` (`TopologicalSpace.denseSeq`). The weighted synthesis of
`TauCeti.Analysis.LocallyConvex.WeightedSynthesis`, with the testing elements `e ν` and the bounds
`N_m(e ν)` given by the defining seminorms of `𝓓^{n}_{K}(E, F)`, then produces the separable Banach
space `TauCeti.SupportedInCarrier E F n K`, in the manner of Floer's space `C_ε`. It comes with a
continuous injective linear map into `𝓓^{n}_{K}(E, F)`
(`TauCeti.supportedInCarrierMap_injective`) with dense range
(`TauCeti.denseRange_supportedInCarrierMap`), and each seminorm `N_m` is bounded on it by a
multiple of the norm (`TauCeti.exists_seminorm_supportedInCarrierMap_le`). So the elements of the
carrier are honest `C^n` functions supported in `K`, every `C^m` norm with `m ≤ n` is controlled by
the Banach norm, and every continuous linear functional on `𝓓^{n}_{K}(E, F)` that vanishes on the
carrier vanishes identically.

## Main definitions

* `TauCeti.SupportedInCarrier E F n K`: the separable Banach carrier of `C^n` functions supported
  in `K`.
* `TauCeti.supportedInCarrierMap E F n K`: its continuous injective linear map into
  `𝓓^{n}_{K}(E, F)`.

## Main results

* `TauCeti.supportedInCarrierMap_injective`, `TauCeti.denseRange_supportedInCarrierMap`: the map
  into `𝓓^{n}_{K}(E, F)` is injective with dense range.
* `TauCeti.exists_supportedInCarrierMap_eq_denseSeq`: every term of the dense sequence
  `TopologicalSpace.denseSeq 𝓓^{n}_{K}(E, F)` on which the carrier is built lies in its range.
* `TauCeti.exists_seminorm_supportedInCarrierMap_le`: every defining seminorm of
  `𝓓^{n}_{K}(E, F)` is bounded on the carrier.

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813, Section 5 (the space `C_ε` of smooth perturbations).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 3.2.
-/

public section

open TopologicalSpace
open scoped Distributions NNReal

namespace TauCeti

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F] (n : ℕ∞) (K : Compacts E)

/-- **The separable Banach carrier of `C^n` functions supported in `K`.** It is the synthesis
carrier (`TauCeti.SynthesisCarrier`) of a dense sequence of `𝓓^{n}_{K}(E, F)`, weighted by the
values of the defining seminorms `N_m` on it. -/
def SupportedInCarrier : Type :=
  SynthesisCarrier (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
    Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

noncomputable instance : NormedAddCommGroup (SupportedInCarrier E F n K) :=
  inferInstanceAs <| NormedAddCommGroup <|
    SynthesisCarrier (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
      Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

noncomputable instance : NormedSpace ℝ (SupportedInCarrier E F n K) :=
  inferInstanceAs <| NormedSpace ℝ <|
    SynthesisCarrier (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
      Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

instance : CompleteSpace (SupportedInCarrier E F n K) :=
  inferInstanceAs <| CompleteSpace <|
    SynthesisCarrier (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
      Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

instance : SeparableSpace (SupportedInCarrier E F n K) :=
  inferInstanceAs <| SeparableSpace <|
    SynthesisCarrier (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
      Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

/-- The continuous injective linear map from the carrier `TauCeti.SupportedInCarrier E F n K` into
`𝓓^{n}_{K}(E, F)`. -/
noncomputable def supportedInCarrierMap : SupportedInCarrier E F n K →L[ℝ] 𝓓^{n}_{K}(E, F) :=
  synthesisCarrierMap (ContDiffMapSupportedIn.withSeminorms ℝ E F n K) fun m ν ↦
    Real.le_coe_toNNReal (ContDiffMapSupportedIn.seminorm ℝ E F n K m (denseSeq _ ν))

/-- The carrier maps injectively into `𝓓^{n}_{K}(E, F)`. -/
theorem supportedInCarrierMap_injective : Function.Injective (supportedInCarrierMap E F n K) :=
  synthesisCarrierMap_injective _ _

/-- The carrier is dense in `𝓓^{n}_{K}(E, F)`. -/
theorem denseRange_supportedInCarrierMap : DenseRange (supportedInCarrierMap E F n K) :=
  denseRange_synthesisCarrierMap _ _ ((denseRange_denseSeq _).mono Submodule.subset_span)

/-- Every term of the dense sequence of `𝓓^{n}_{K}(E, F)` on which the carrier is built lies in its
range. -/
theorem exists_supportedInCarrierMap_eq_denseSeq (ν : ℕ) :
    ∃ x, supportedInCarrierMap E F n K x = denseSeq 𝓓^{n}_{K}(E, F) ν :=
  exists_synthesisCarrierMap_eq _ _ ν

/-- Each defining seminorm `N_m` of `𝓓^{n}_{K}(E, F)` is bounded on the carrier by a multiple of
its norm. -/
theorem exists_seminorm_supportedInCarrierMap_le (m : ℕ) :
    ∃ C : ℝ≥0, ∀ x : SupportedInCarrier E F n K,
      ContDiffMapSupportedIn.seminorm ℝ E F n K m (supportedInCarrierMap E F n K x) ≤ C * ‖x‖ :=
  ⟨_, seminorm_synthesisCarrierMap_le _ _ m⟩

end TauCeti
