/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr

/-!
# Transporting finite Galois subextensions between separable closures

Let `L/K` be embedded in `Kˢ` by `σ`, and let `E/L` be embedded in `Kˢ` compatibly with `σ`.
The chosen identification `separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` transports this
embedding to an `L`-embedding in `Lˢ`. If `E/L` is finite and normal, its image is a finite
Galois subextension of `Lˢ/L`, with an algebra equivalence recording the ambient embedding.

This supplies finite fields and compatible coefficient maps for comparing finite cocycle
restriction with restriction on absolute Galois cohomology. In particular, a finite Galois
extension of `K` containing the image of `L` can be read inside the separable closure of `L`.
No normality of `L/K` is needed.

A field isomorphism `e : K ≃+* L`, with `K` and `L` in independent universes, transports every
intermediate field of `Kˢ/K` to one of `Lˢ/L` through the chosen identification
`e.separableClosureCongr : Lˢ ≃+* Kˢ`. Finiteness, degree, normality and the Galois property
are preserved, each subextension is identified with its transport by a ring isomorphism
semilinear over `e`, and their automorphism groups are identified compatibly with it. These are
the finite coefficient fields, coefficient maps and automorphism maps along which a finite
`2`-cocycle over `K` is transported to one over `L`, for instance when `L` is the universe lift
`ULift K`.

## Main definitions

* `AlgHom.liftToSeparableClosure`: an embedding of `E` into `Kˢ` compatible with `σ`, read as an
  `L`-embedding into `Lˢ`.
* `RingEquiv.intermediateFieldCongr e`: the order isomorphism between the intermediate fields of
  `Kˢ/K` and of `Lˢ/L` induced by `e : K ≃+* L`.
* `RingEquiv.intermediateFieldCongrEquiv e E`: the ring isomorphism from `E` to its transport.
* `RingEquiv.intermediateFieldAutCongr e E`: the induced isomorphism from the automorphism group
  of the transport of `E` over `L` to the automorphism group of `E` over `K`.

## Main results

* `AlgHom.exists_finiteGalois_subextension_equiv`: a finite normal extension of `L` embedded
  compatibly in `Kˢ` is isomorphic to a finite Galois subextension of `Lˢ/L`.
* `RingEquiv.finrank_intermediateFieldCongr`, `RingEquiv.normal_intermediateFieldCongr`,
  `RingEquiv.isGalois_intermediateFieldCongr`: transport preserves degree, normality and the
  Galois property.
* `RingEquiv.intermediateFieldCongrEquiv_intermediateFieldAutCongr`: the ring isomorphism
  intertwines corresponding automorphisms.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VI, §1.
-/

public section

noncomputable section

namespace AlgHom

open TauCeti

universe u v w

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {E : Type w} [Field E] [Algebra K E] [Algebra L E]

/-- Transport a compatible embedding of `E` into `Kˢ` to an `L`-embedding into `Lˢ`, using
the chosen identification of separable closures extending `σ`. -/
def liftToSeparableClosure (σ : L →ₐ[K] SeparableClosure K)
    (ι : E →ₐ[K] SeparableClosure K) (hι : ∀ x : L, ι (algebraMap L E x) = σ x) :
    E →ₐ[L] SeparableClosure L :=
  { (separableClosureRingEquiv K L σ).symm.toRingHom.comp ι.toRingHom with
    commutes' x := by
      simp [hι] }

/-- The transported embedding is the original embedding followed by the inverse
identification of separable closures. -/
theorem liftToSeparableClosure_apply (σ : L →ₐ[K] SeparableClosure K)
    (ι : E →ₐ[K] SeparableClosure K) (hι : ∀ x : L, ι (algebraMap L E x) = σ x) (y : E) :
    σ.liftToSeparableClosure ι hι y = (separableClosureRingEquiv K L σ).symm (ι y) :=
  (rfl)

/-- The two ambient embeddings agree through the identification of separable closures. -/
@[simp]
theorem separableClosureRingEquiv_liftToSeparableClosure
    (σ : L →ₐ[K] SeparableClosure K) (ι : E →ₐ[K] SeparableClosure K)
    (hι : ∀ x : L, ι (algebraMap L E x) = σ x) (y : E) :
    separableClosureRingEquiv K L σ (σ.liftToSeparableClosure ι hι y) = ι y := by
  rw [liftToSeparableClosure_apply, RingEquiv.apply_symm_apply]

/-- A finite normal extension embedded compatibly in `Kˢ` is isomorphic to a finite Galois
subextension of `Lˢ/L`. The equivalence preserves the specified embedding into `Kˢ` through
the chosen identification of separable closures. -/
theorem exists_finiteGalois_subextension_equiv [FiniteDimensional L E] [Normal L E]
    (σ : L →ₐ[K] SeparableClosure K) (ι : E →ₐ[K] SeparableClosure K)
    (hι : ∀ x : L, ι (algebraMap L E x) = σ x) :
    ∃ M : IntermediateField L (SeparableClosure L),
      FiniteDimensional L M ∧ IsGalois L M ∧
        ∃ e : E ≃ₐ[L] M, ∀ y : E,
          separableClosureRingEquiv K L σ (e y : SeparableClosure L) = ι y := by
  let f := σ.liftToSeparableClosure ι hι
  have : FiniteDimensional L f.fieldRange := f.toLinearMap.finiteDimensional_range
  refine ⟨f.fieldRange, inferInstance, IsGalois.mk, f.equivFieldRange, fun y ↦ ?_⟩
  rw [equivFieldRange_apply_coe]
  exact separableClosureRingEquiv_liftToSeparableClosure σ ι hι y

end AlgHom

namespace RingEquiv

open TauCeti

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] (e : K ≃+* L)

/-- A field isomorphism `e : K ≃+* L` identifies the intermediate fields of `Kˢ/K` with those of
`Lˢ/L`. The intermediate field `E` goes to its image under the inverse of the chosen
identification `e.separableClosureCongr : Lˢ ≃+* Kˢ`, which extends `e.symm`. -/
def intermediateFieldCongr :
    IntermediateField K (SeparableClosure K) ≃o IntermediateField L (SeparableClosure L) where
  toFun E := (E.toSubfield.comap e.separableClosureCongr.toRingHom).toIntermediateField
    fun y ↦ by simp
  invFun F := (F.toSubfield.comap e.separableClosureCongr.symm.toRingHom).toIntermediateField
    fun x ↦ by simp
  -- Membership in either transport is by definition membership of the image under the chosen
  -- identification, so each identity below is the corresponding cancellation of that equivalence.
  left_inv E := IntermediateField.ext fun x ↦
    Iff.of_eq (congrArg (· ∈ E) (e.separableClosureCongr.apply_symm_apply x))
  right_inv F := IntermediateField.ext fun y ↦
    Iff.of_eq (congrArg (· ∈ F) (e.separableClosureCongr.symm_apply_apply y))
  map_rel_iff' {E E'} := by
    refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ h hy⟩
    have hx' : e.separableClosureCongr (e.separableClosureCongr.symm x) ∈ E := by
      rwa [apply_symm_apply]
    have h' : e.separableClosureCongr (e.separableClosureCongr.symm x) ∈ E' := h hx'
    rwa [apply_symm_apply] at h'

variable {e}

/-- An element of `Lˢ` lies in the transported intermediate field exactly when its image in `Kˢ`
under the chosen identification lies in the original one. -/
@[simp]
theorem mem_intermediateFieldCongr {E : IntermediateField K (SeparableClosure K)}
    {y : SeparableClosure L} :
    y ∈ e.intermediateFieldCongr E ↔ e.separableClosureCongr y ∈ E :=
  Iff.rfl

/-- An element of `Kˢ` lies in the inverse transport of an intermediate field of `Lˢ/L` exactly
when its image under the inverse identification lies in that intermediate field. -/
@[simp]
theorem mem_intermediateFieldCongr_symm {F : IntermediateField L (SeparableClosure L)}
    {x : SeparableClosure K} :
    x ∈ e.intermediateFieldCongr.symm F ↔ e.separableClosureCongr.symm x ∈ F :=
  Iff.rfl

variable (e) (E : IntermediateField K (SeparableClosure K))

/-- The ring isomorphism from an intermediate field `E` of `Kˢ/K` to its transport, given by the
inverse of the chosen identification of separable closures. It is semilinear over `e`
(`intermediateFieldCongrEquiv_algebraMap`). -/
def intermediateFieldCongrEquiv : E ≃+* e.intermediateFieldCongr E where
  toFun x := ⟨e.separableClosureCongr.symm x, by simp⟩
  invFun y := ⟨e.separableClosureCongr y, y.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_add' x y := by
    ext
    simp

/-- The transport of an element of `E` is its image under the inverse of the chosen
identification of separable closures. -/
@[simp]
theorem coe_intermediateFieldCongrEquiv (x : E) :
    (e.intermediateFieldCongrEquiv E x : SeparableClosure L) = e.separableClosureCongr.symm x :=
  (rfl)

/-- The inverse transport of an element is its image under the chosen identification of
separable closures. -/
@[simp]
theorem coe_intermediateFieldCongrEquiv_symm (y : e.intermediateFieldCongr E) :
    ((e.intermediateFieldCongrEquiv E).symm y : SeparableClosure K) = e.separableClosureCongr y :=
  (rfl)

/-- The transport of an intermediate field is semilinear over `e`. -/
@[simp]
theorem intermediateFieldCongrEquiv_algebraMap (x : K) :
    e.intermediateFieldCongrEquiv E (algebraMap K E x) =
      algebraMap L (e.intermediateFieldCongr E) (e x) := by
  ext
  simp

/-- The inverse transport of an intermediate field is semilinear over `e.symm`. -/
@[simp]
theorem intermediateFieldCongrEquiv_symm_algebraMap (y : L) :
    (e.intermediateFieldCongrEquiv E).symm (algebraMap L (e.intermediateFieldCongr E) y) =
      algebraMap K E (e.symm y) := by
  rw [RingEquiv.symm_apply_eq, intermediateFieldCongrEquiv_algebraMap, e.apply_symm_apply]

/-- The semilinearity of `intermediateFieldCongrEquiv` over `e`, as an equation of ring
homomorphisms; this is the compatibility consumed by Mathlib's `*_of_equiv_equiv` transfers. -/
theorem algebraMap_comp_intermediateFieldCongrEquiv :
    (algebraMap L (e.intermediateFieldCongr E)).comp (e : K →+* L) =
      (e.intermediateFieldCongrEquiv E : E →+* e.intermediateFieldCongr E).comp
        (algebraMap K E) :=
  RingHom.ext fun x ↦ (intermediateFieldCongrEquiv_algebraMap e E x).symm

/-- **Transport preserves degree.** -/
@[simp]
theorem finrank_intermediateFieldCongr :
    Module.finrank L (e.intermediateFieldCongr E) = Module.finrank K E :=
  (Algebra.finrank_eq_of_equiv_equiv e (e.intermediateFieldCongrEquiv E)
    (algebraMap_comp_intermediateFieldCongrEquiv e E)).symm

instance finiteDimensional_intermediateFieldCongr [FiniteDimensional K E] :
    FiniteDimensional L (e.intermediateFieldCongr E) :=
  .of_equiv_equiv e (e.intermediateFieldCongrEquiv E)
    (algebraMap_comp_intermediateFieldCongrEquiv e E)

instance normal_intermediateFieldCongr [Normal K E] : Normal L (e.intermediateFieldCongr E) :=
  .of_equiv_equiv (algebraMap_comp_intermediateFieldCongrEquiv e E)

instance isGalois_intermediateFieldCongr [IsGalois K E] :
    IsGalois L (e.intermediateFieldCongr E) :=
  .of_equiv_equiv (algebraMap_comp_intermediateFieldCongrEquiv e E)

/-- The automorphism groups of an intermediate field `E` of `Kˢ/K` and of its transport are
identified by conjugation with `intermediateFieldCongrEquiv`. Like `absoluteGaloisGroupCongr`,
the identification is contravariant in `e`. -/
def intermediateFieldAutCongr :
    (e.intermediateFieldCongr E ≃ₐ[L] e.intermediateFieldCongr E) ≃* (E ≃ₐ[K] E) where
  toFun g := AlgEquiv.ofRingEquiv
    (f := ((e.intermediateFieldCongrEquiv E).trans g.toRingEquiv).trans
      (e.intermediateFieldCongrEquiv E).symm)
    fun x ↦ by simp
  invFun g := AlgEquiv.ofRingEquiv
    (f := ((e.intermediateFieldCongrEquiv E).symm.trans g.toRingEquiv).trans
      (e.intermediateFieldCongrEquiv E))
    fun y ↦ by simp
  left_inv g := by
    ext
    simp
  right_inv g := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

/-- The automorphism of `E` corresponding to an automorphism `g` of its transport is
conjugation of `g` by `intermediateFieldCongrEquiv`. -/
@[simp]
theorem intermediateFieldAutCongr_apply
    (g : e.intermediateFieldCongr E ≃ₐ[L] e.intermediateFieldCongr E) (x : E) :
    e.intermediateFieldAutCongr E g x =
      (e.intermediateFieldCongrEquiv E).symm (g (e.intermediateFieldCongrEquiv E x)) :=
  (rfl)

/-- **The automorphism identification is compatible with the transport of elements**:
`intermediateFieldCongrEquiv` intertwines an automorphism of the transport with the corresponding
automorphism of `E`. -/
theorem intermediateFieldCongrEquiv_intermediateFieldAutCongr
    (g : e.intermediateFieldCongr E ≃ₐ[L] e.intermediateFieldCongr E) (x : E) :
    e.intermediateFieldCongrEquiv E (e.intermediateFieldAutCongr E g x) =
      g (e.intermediateFieldCongrEquiv E x) := by
  simp

/-- The inverse automorphism identification is conjugation by `intermediateFieldCongrEquiv`. -/
@[simp]
theorem intermediateFieldAutCongr_symm_apply (g : E ≃ₐ[K] E) (y : e.intermediateFieldCongr E) :
    (e.intermediateFieldAutCongr E).symm g y =
      e.intermediateFieldCongrEquiv E (g ((e.intermediateFieldCongrEquiv E).symm y)) :=
  (rfl)

end RingEquiv
