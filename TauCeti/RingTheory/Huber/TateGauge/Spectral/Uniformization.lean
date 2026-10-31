/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Uniform
public import TauCeti.RingTheory.Huber.TateGauge.Spectral.Topology

/-!
# The uniformization of a Tate Huber pair

Let `A` be a Tate ring. Its *uniformization* `A^u` is the separated completion of `A` for its
spectral topology `SpectralTop A`, that is, for the spectral seminorm `|·|_sp` of any norm datum.
It is a complete Hausdorff uniform Tate ring, and the canonical map `ι : A → A^u` is continuous,
has dense image, and kills exactly the elements with `|x|_sp = 0`. For a Huber pair `(A, A⁺)` the
plus ring `A^{u+}` is the closure of `ι(A⁺)`, and `ι` is a morphism of Huber pairs
`(A, A⁺) → (A^u, A^{u+})`.

Uniformization is left adjoint to the inclusion of complete Hausdorff uniform Huber pairs: every
morphism `(A, A⁺) → (B, B⁺)` into a complete Hausdorff Huber pair with `B` uniform factors
uniquely through `ι`. The key input is that a continuous homomorphism into a uniform ring is
continuous for the spectral topology of its source
(`TauCeti.Huber.SpectralTop.continuous_comp_toSpectralTop_symm`). In particular, when `A` is
itself complete, Hausdorff and uniform, `ι` is an isomorphism.

## Main definitions

* `TauCeti.Huber.Uniformization A`: the complete Hausdorff uniform Tate ring `A^u`.
* `TauCeti.Huber.toUniformization A`: the canonical map `ι : A →+* A^u`.
* `TauCeti.Huber.Uniformization.lift`: the extension to `A^u` of a continuous homomorphism into
  a complete Hausdorff uniform ring.
* `TauCeti.Huber.Pair.uniformization`: the Huber pair `(A^u, A^{u+})`.
* `TauCeti.Huber.Pair.uniformizationHom`: `ι` as a morphism of Huber pairs.
* `TauCeti.Huber.Pair.Hom.uniformizationLift`: the factorisation of a morphism into a complete
  Hausdorff uniform Huber pair through `ι`.

## Main results

* `TauCeti.Huber.denseRange_toUniformization`: `ι` has dense range.
* `TauCeti.Huber.toUniformization_eq_zero_iff`: `ι x = 0` if and only if `|x|_sp = 0`.
* `TauCeti.Huber.Uniformization.ringHom_ext`: continuous homomorphisms out of `A^u` are
  determined on the image of `ι`.
* `TauCeti.Huber.isHomeomorph_toUniformization`: for complete Hausdorff uniform `A`, `ι` is a
  homeomorphism.
* `TauCeti.Huber.Pair.uniformization_plus`: `A^{u+}` is the closure of `ι(A⁺)`.
* `TauCeti.Huber.Pair.Hom.uniformizationLift_comp_uniformizationHom` and
  `TauCeti.Huber.Pair.Hom.ext_uniformization`: the universal property of the uniformization.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.8.13.
* D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*, §2, Remark 2.11.
-/

public section

open Topology UniformSpace

namespace TauCeti.Huber

section Ring

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- The *uniformization* `A^u` of a Tate ring `A`: the separated completion of `A` for its
spectral topology (Kedlaya–Liu, Definition 2.8.13). It is a complete Hausdorff Tate ring
(`TauCeti.Huber.IsTateRing.completion`) and it is uniform (`TauCeti.Huber.IsUniform.completion`,
as `SpectralTop A` is uniform). -/
abbrev Uniformization := Completion (SpectralTop A)

/-- The canonical map `ι : A → A^u`: the continuous identity `A → SpectralTop A` followed by the
completion map. -/
noncomputable def toUniformization : A →+* Uniformization A :=
  Completion.coeRingHom.comp (toSpectralTop A : A →+* SpectralTop A)

variable {A}

/-- `ι x` is the image in the completion of `x`, viewed in the spectral topology. -/
theorem toUniformization_apply (x : A) :
    toUniformization A x = ((toSpectralTop A x : SpectralTop A) : Completion (SpectralTop A)) :=
  (rfl)

/-- The canonical map `ι : A → A^u` is continuous. -/
@[fun_prop]
theorem continuous_toUniformization : Continuous (toUniformization A) :=
  (Completion.continuous_coe _).comp SpectralTop.continuous_toSpectralTop

/-- The canonical map `ι : A → A^u` has dense range. -/
theorem denseRange_toUniformization : DenseRange (toUniformization A) :=
  Completion.denseRange_coe.comp (toSpectralTop A).surjective.denseRange
    (Completion.continuous_coe _)

/-- **The kernel of the uniformization map**: `ι x = 0` exactly when the spectral seminorm of `x`
vanishes, for any norm datum `d`. -/
theorem toUniformization_eq_zero_iff (d : TateNormDatum A) {x : A} :
    toUniformization A x = 0 ↔ spectralSeminorm d x = 0 := by
  -- `ι x = 0` says that `x` and `0` are inseparable in `SpectralTop A`, that is, that `x` lies in
  -- every ball of the spectral seminorm around zero
  rw [toUniformization_apply, ← Completion.coe_zero, ← inseparable_iff_eq,
    (Completion.isUniformInducing_coe _).isInducing.inseparable_iff, ← specializes_iff_inseparable,
    specializes_iff_pure, (SpectralTop.hasBasis_nhds_zero_spectralSeminorm d).ge_iff]
  simp only [Filter.mem_pure, (toSpectralTop A).injective.mem_set_image, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ by simpa using h ε hε)
    (apply_nonneg _ x), fun h ε hε ↦ h ▸ hε⟩

namespace Uniformization

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsUniform B]

/-- **The universal property of the uniformization, at ring level**: a continuous homomorphism
`φ : A → B` into a complete Hausdorff uniform ring extends to `A^u`. It is continuous for the
spectral topology of `A` (`TauCeti.Huber.SpectralTop.continuous_comp_toSpectralTop_symm`), hence
extends to the completion. -/
noncomputable def lift (φ : A →+* B) (hφ : Continuous φ) : Uniformization A →+* B :=
  Completion.extensionHom (φ.comp ((toSpectralTop A).symm : SpectralTop A →+* A))
    (SpectralTop.continuous_comp_toSpectralTop_symm hφ)

/-- The extension of `φ` to `A^u` is continuous. -/
@[fun_prop]
theorem continuous_lift (φ : A →+* B) (hφ : Continuous φ) : Continuous (lift φ hφ) :=
  Completion.continuous_extension

/-- The extension of `φ` to `A^u` restricts to `φ` along `ι`. -/
@[simp]
theorem lift_toUniformization (φ : A →+* B) (hφ : Continuous φ) (x : A) :
    lift φ hφ (toUniformization A x) = φ x := by
  rw [toUniformization_apply]
  exact (Completion.extensionHom_coe _ _ (toSpectralTop A x)).trans (by simp)

/-- The extension of `φ` to `A^u` restricts to `φ` along `ι`, as ring homomorphisms. -/
@[simp]
theorem lift_comp_toUniformization (φ : A →+* B) (hφ : Continuous φ) :
    (lift φ hφ).comp (toUniformization A) = φ :=
  RingHom.ext (lift_toUniformization φ hφ)

/-- **Continuous homomorphisms out of `A^u` are determined on the image of `ι`**, for a Hausdorff
target. -/
theorem ringHom_ext {C : Type*} [Semiring C] [TopologicalSpace C] [T2Space C]
    {f g : Uniformization A →+* C} (hf : Continuous f) (hg : Continuous g)
    (h : f.comp (toUniformization A) = g.comp (toUniformization A)) : f = g :=
  RingHom.coe_inj <| denseRange_toUniformization.equalizer hf hg <| congrArg DFunLike.coe h

end Uniformization

end Ring

section Complete

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A]

/-- **A complete Hausdorff uniform Tate ring is its own uniformization**: `ι : A → A^u` is a
homeomorphism, with inverse the extension of the identity of `A`. -/
theorem isHomeomorph_toUniformization [CompleteSpace A] [T0Space A] [IsUniform A] :
    IsHomeomorph (toUniformization A) := by
  let r := Uniformization.lift (RingHom.id A) continuous_id
  have hr : Continuous r := Uniformization.continuous_lift _ _
  have hιr : (toUniformization A).comp r = RingHom.id (Uniformization A) :=
    Uniformization.ringHom_ext (continuous_toUniformization.comp hr) continuous_id
      (RingHom.ext fun x ↦ by simp [r])
  exact (Homeomorph.mk ⟨toUniformization A, r, fun x ↦ by simp [r],
    RingHom.congr_fun hιr⟩ continuous_toUniformization
    hr).isHomeomorph

end Complete

namespace Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **The uniformization `(A^u, A^{u+})` of a Tate Huber pair `(A, A⁺)`**: the completion of the
pair `(SpectralTop A, A⁺)`. Its plus ring is the closure of `ι(A⁺)` (`uniformization_plus`)
(Kedlaya–Liu, Definition 2.8.13). -/
noncomputable def uniformization (S : Pair A) : Pair (Uniformization A) :=
  (SpectralTop.pair S).completion

/-- The plus ring `A^{u+}` of the uniformization is the closure of the image of `A⁺` under `ι`. -/
theorem uniformization_plus (S : Pair A) :
    S.uniformization.plus = (S.plus.map (toUniformization A)).topologicalClosure := by
  have h : (SpectralTop.pair S).plus = S.plus.map (toSpectralTop A : A →+* SpectralTop A) := by
    ext x
    rw [SpectralTop.mem_pair_plus, Subring.mem_map_equiv]
  rw [uniformization, completion_plus, completionPlus_def, h, Subring.map_map, toUniformization]

/-- **The uniformization map `ι : (A, A⁺) → (A^u, A^{u+})`** as a morphism of Huber pairs. -/
noncomputable def uniformizationHom (S : Pair A) : Hom S S.uniformization :=
  (SpectralTop.pair S).completionHom.comp (SpectralTop.pairHom S)

/-- The underlying ring homomorphism of `uniformizationHom S` is `ι`. -/
@[simp]
theorem Hom.toRingHom_uniformizationHom (S : Pair A) :
    S.uniformizationHom.toRingHom = toUniformization A := by
  rw [uniformizationHom, Hom.toRingHom_comp, toRingHom_completionHom,
    SpectralTop.toRingHom_pairHom, toUniformization]

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B] [IsUniform B] {S : Pair A} {T : Pair B}

/-- **The universal property of the uniformization**: a morphism `f : (A, A⁺) → (B, B⁺)` into a
complete Hausdorff Huber pair with `B` uniform factors through `ι` (Kedlaya–Liu, Definition
2.8.13). The factorisation is unique by `TauCeti.Huber.Pair.Hom.ext_uniformization`. -/
noncomputable def Hom.uniformizationLift (f : Hom S T) : Hom S.uniformization T :=
  Hom.extension (S := SpectralTop.pair S)
    { toRingHom := f.toRingHom.comp ((toSpectralTop A).symm : SpectralTop A →+* A)
      continuous_toRingHom := SpectralTop.continuous_comp_toSpectralTop_symm f.continuous_toRingHom
      map_mem_plus := fun _ ha ↦ f.map_mem_plus _ (SpectralTop.mem_pair_plus.mp ha) }

/-- The underlying ring homomorphism of `f.uniformizationLift` is the ring-level extension
`TauCeti.Huber.Uniformization.lift`. -/
theorem Hom.toRingHom_uniformizationLift (f : Hom S T) :
    f.uniformizationLift.toRingHom = Uniformization.lift f.toRingHom f.continuous_toRingHom :=
  Hom.toRingHom_extension _

/-- The factorisation `f.uniformizationLift` restricts to `f` along `ι`. -/
@[simp]
theorem Hom.uniformizationLift_comp_uniformizationHom (f : Hom S T) :
    f.uniformizationLift.comp S.uniformizationHom = f := by
  ext x
  simp [Hom.toRingHom_uniformizationLift]

/-- **Morphisms out of the uniformization are determined on `A`**: two morphisms into a
Hausdorff Huber pair that agree after `ι` are equal. -/
theorem Hom.ext_uniformization {C : Type*} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [T2Space C] [IsHuberRing C] {U : Pair C}
    {g h : Hom S.uniformization U}
    (hgh : g.comp S.uniformizationHom = h.comp S.uniformizationHom) : g = h :=
  Hom.ext <| Uniformization.ringHom_ext g.continuous_toRingHom h.continuous_toRingHom <| by
    simpa using congrArg Hom.toRingHom hgh

end Pair

namespace Pair

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T0Space A] [IsUniform A]

/-- **A complete Hausdorff uniform Tate Huber pair is its own uniformization**: `ι` is an
isomorphism of Huber pairs, with inverse the factorisation of the identity. This direction
composes to the identity of `(A^u, A^{u+})`; the other is
`TauCeti.Huber.Pair.Hom.uniformizationLift_comp_uniformizationHom` for the identity. -/
theorem uniformizationHom_comp_uniformizationLift_id (S : Pair A) :
    S.uniformizationHom.comp (Hom.id S).uniformizationLift = Hom.id S.uniformization :=
  Hom.ext_uniformization <| by
    rw [Hom.comp_assoc, Hom.uniformizationLift_comp_uniformizationHom, Hom.comp_id, Hom.id_comp]

end Pair

end TauCeti.Huber
