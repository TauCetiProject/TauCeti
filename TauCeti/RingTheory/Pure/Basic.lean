/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import TauCeti.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.Flat.Extensions

/-!
# Pure (universally injective) linear maps

A linear map `f : M → N` of modules over a commutative ring `R` is *pure*, or *universally
injective*, if `P ⊗[R] M → P ⊗[R] N` is injective for every `R`-module `P`. Pure maps are
injective, and they are the maps along which injectivity survives every base change; for
instance the unit `R → S` of an algebra is pure when `S` is faithfully flat over `R`, or when it
has an `R`-linear retraction. Purity is a module-theoretic notion, distinct from the spectral
universal injectivity of a morphism of schemes.

The definition quantifies over test modules `P` in the universe of `R`. The first main result
shows that finitely presented test modules already suffice, and consequently that the
definition does not depend on this choice of universe: a pure map stays injective after
tensoring with a module in any universe (`LinearMap.IsPure.lTensor_injective`).

## Main definitions

* `LinearMap.IsPure`: `f : M →ₗ[R] N` is pure if `f.lTensor P` is injective for every `P`.

## Main results

* `LinearMap.isPure_iff_forall_finitePresentation`: purity can be tested on finitely presented
  modules.
* `LinearMap.IsPure.lTensor_injective`, `LinearMap.IsPure.rTensor_injective`: a pure map stays
  injective after tensoring, on either side, with a module in any universe.
* `LinearMap.IsPure.injective`: pure maps are injective.
* `LinearMap.IsPure.comp`, `LinearMap.IsPure.of_comp`: pure maps are closed under composition, and
  if `g ∘ f` is pure then so is `f`.
* `LinearMap.isPure_of_comp_eq_id`: split injections are pure.
* `LinearMap.IsPure.lTensor`, `LinearMap.IsPure.rTensor`, `LinearMap.IsPure.baseChange`,
  `LinearMap.IsPure.restrictScalars`: purity is stable under tensoring with a module, under base
  change and under restriction of scalars.
* `LinearMap.isPure_of_exact_of_flat`, `LinearMap.IsPure.flat_of_exact`: an injective map with
  flat cokernel is pure, and the cokernel of a pure map into a flat module is flat; so an
  injective map into a flat module is pure exactly when its cokernel is flat
  (`LinearMap.isPure_iff_flat_of_exact`, `Submodule.isPure_subtype_iff_flat`).
* `LinearMap.IsPure.flat_of_flat`: flatness descends along pure maps; the source of a pure map
  into a flat module is flat.
* `Ideal.pure_iff_isPure_subtype`: an ideal is pure in Mathlib's sense (`R ⧸ I` flat) exactly
  when its inclusion into `R` is a pure map.
* `Ideal.subtype_rTensor_injective_of_pure`: consequently, for a pure ideal `I` the map
  `I ⊗[R] M → R ⊗[R] M` is injective for every module `M`.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), Annexe A,
  Lemmes A.1.1 and A.2.1.
* H. Matsumura, *Commutative ring theory*, Appendix to §7 (pure submodules).
* The Stacks Project, Section *Universally injective module maps*.
-/

public section

open TensorProduct

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A linear map `f : M →ₗ[R] N` is *pure* (or *universally injective*) if
`f.lTensor P : P ⊗[R] M → P ⊗[R] N` is injective for every `R`-module `P` in the universe of `R`.
By `LinearMap.IsPure.lTensor_injective` the same then holds for modules in every universe. -/
def IsPure (f : M →ₗ[R] N) : Prop :=
  ∀ (P : Type u) [AddCommGroup P] [Module R P], Function.Injective (f.lTensor P)

/-- Unfolding `LinearMap.IsPure`: injectivity of `f.lTensor P` for every `P` in the universe of
`R`. -/
theorem isPure_iff {f : M →ₗ[R] N} :
    f.IsPure ↔ ∀ (P : Type u) [AddCommGroup P] [Module R P], Function.Injective (f.lTensor P) :=
  Iff.rfl

/-- If `f.lTensor Q` is injective for every finitely presented module `Q` in the universe of `R`,
then `f.lTensor P` is injective for every finite module `P`, in any universe. Writing `P` as a
quotient of `Rⁿ` by `K`, an element of the kernel lifts to `Rⁿ ⊗ M`, and its image in `Rⁿ ⊗ N`
comes from a finitely generated submodule `L` of `K`; it already vanishes in `(Rⁿ ⧸ L) ⊗ N`. -/
private theorem lTensor_injective_of_finite {f : M →ₗ[R] N}
    (H : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
      Function.Injective (f.lTensor Q))
    (P : Type*) [AddCommGroup P] [Module R P] [Module.Finite R P] :
    Function.Injective (f.lTensor P) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := rTensor_surjective M hπ x
  rw [lTensor_rTensor_comm] at hx
  -- The image of `y` in `Rⁿ ⊗ N` comes from `ker π ⊗ N`, and in fact from `L ⊗ N` for a finitely
  -- generated submodule `L` of `ker π`.
  obtain ⟨z, hz⟩ := (rTensor_exact N (exact_subtype_ker_map π) hπ _).mp hx
  obtain ⟨L, hL, z, rfl⟩ := TensorProduct.exists_of_fg z
  let L' : Submodule R (Fin n → R) := L.map (ker π).subtype
  have hL' : L' ≤ ker π := Submodule.map_subtype_le _ _
  have : Module.FinitePresentation R ((Fin n → R) ⧸ L') :=
    Module.finitePresentation_of_free_of_surjective L'.mkQ L'.mkQ_surjective
      (by rw [Submodule.ker_mkQ]; exact hL.map _)
  -- The image of `y` in `(Rⁿ ⧸ L) ⊗ M` lies in the kernel of `f.lTensor`, so it vanishes.
  have hzero : L'.mkQ ∘ₗ (ker π).subtype ∘ₗ L.subtype = 0 := by
    ext x
    simp [L']
  have hy : L'.mkQ.rTensor M y = 0 := H _ <| by
    rw [lTensor_rTensor_comm, ← hz]
    simp [← rTensor_comp_apply, hzero]
  rw [← L'.liftQ_mkQ π hL', rTensor_comp_apply, hy, map_zero]

/-- If `f.lTensor Q` is injective for every finitely presented module `Q` in the universe of `R`,
then `f.lTensor P` is injective for every module `P`, in any universe. An element of the kernel
comes from a finitely generated submodule of `P`, and its image already vanishes after enlarging
that submodule to another finitely generated one. -/
theorem lTensor_injective_of_forall_finitePresentation {f : M →ₗ[R] N}
    (H : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
      Function.Injective (f.lTensor Q))
    (P : Type*) [AddCommGroup P] [Module R P] : Function.Injective (f.lTensor P) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨P₀, hP₀, x₀, rfl⟩ := TensorProduct.exists_of_fg x
  rw [lTensor_rTensor_comm] at hx
  obtain ⟨P₁, hP₀₁, hP₁, h⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hP₀ hx
  have : Module.Finite R P₁ := Module.Finite.iff_fg.mpr hP₁
  have hx₁ : (Submodule.inclusion hP₀₁).rTensor M x₀ = 0 :=
    lTensor_injective_of_finite H P₁ <| by rw [lTensor_rTensor_comm, h, map_zero]
  rw [← Submodule.subtype_comp_inclusion _ _ hP₀₁, rTensor_comp_apply, hx₁, map_zero]

/-- **Purity can be tested on finitely presented modules.** -/
theorem isPure_iff_forall_finitePresentation {f : M →ₗ[R] N} :
    f.IsPure ↔ ∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
      Function.Injective (f.lTensor Q) :=
  ⟨fun hf Q _ _ _ ↦ hf Q, fun H P _ _ ↦ lTensor_injective_of_forall_finitePresentation H P⟩

namespace IsPure

variable {f : M →ₗ[R] N}

/-- A pure map stays injective after tensoring on the left with a module in any universe. -/
theorem lTensor_injective (hf : f.IsPure) (P : Type*) [AddCommGroup P] [Module R P] :
    Function.Injective (f.lTensor P) :=
  lTensor_injective_of_forall_finitePresentation (fun Q _ _ _ ↦ hf Q) P

/-- A pure map stays injective after tensoring on the right with a module in any universe. -/
theorem rTensor_injective (hf : f.IsPure) (P : Type*) [AddCommGroup P] [Module R P] :
    Function.Injective (f.rTensor P) :=
  (lTensor_inj_iff_rTensor_inj P f).mp (hf.lTensor_injective P)

/-- A pure map is injective. -/
theorem injective (hf : f.IsPure) : Function.Injective f := by
  intro a b h
  apply (TensorProduct.lid R M).symm.injective
  apply hf.lTensor_injective R
  simp [h]

end IsPure

variable (R M) in
/-- The identity map is pure. -/
@[simp]
theorem isPure_id : (LinearMap.id : M →ₗ[R] M).IsPure := fun P _ _ ↦ by
  rw [lTensor_id]
  exact Function.injective_id

/-- A linear equivalence is pure. -/
@[simp]
theorem _root_.LinearEquiv.isPure (e : M ≃ₗ[R] N) : e.toLinearMap.IsPure := fun P _ _ ↦ by
  rw [← LinearEquiv.coe_lTensor]
  exact (e.lTensor P).injective

/-- A linear map out of a trivial module is pure. -/
theorem isPure_of_subsingleton [Subsingleton M] (f : M →ₗ[R] N) : f.IsPure := fun _ _ _ ↦
  Function.injective_of_subsingleton _

variable {Q : Type*} [AddCommGroup Q] [Module R Q] {f : M →ₗ[R] N} {g : N →ₗ[R] Q}

/-- The composite of pure maps is pure. -/
theorem IsPure.comp (hg : g.IsPure) (hf : f.IsPure) : (g ∘ₗ f).IsPure := fun P _ _ ↦ by
  rw [lTensor_comp, coe_comp]
  exact (hg P).comp (hf P)

/-- If `g ∘ f` is pure, then `f` is pure. -/
theorem IsPure.of_comp (h : (g ∘ₗ f).IsPure) : f.IsPure := fun P _ _ ↦ by
  have := h P
  rw [lTensor_comp, coe_comp] at this
  exact this.of_comp

/-- **Split injections are pure**: a linear map with a linear left inverse is pure. -/
theorem isPure_of_comp_eq_id {g : N →ₗ[R] M} (h : g ∘ₗ f = LinearMap.id) : f.IsPure :=
  IsPure.of_comp (g := g) (h ▸ isPure_id R M)

/-- Tensoring a pure map on the left with a module gives a pure map. -/
theorem IsPure.lTensor (hf : f.IsPure) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    (f.lTensor Q).IsPure := fun P _ _ ↦ by
  -- `P ⊗ (Q ⊗ -)` is identified with `(P ⊗ Q) ⊗ -` by the associator.
  have : (f.lTensor Q).lTensor P =
      (TensorProduct.assoc R P Q N) ∘ₗ f.lTensor (P ⊗[R] Q) ∘ₗ
        (TensorProduct.assoc R P Q M).symm := by
    rw [lTensor_tensor]
    ext
    simp
  simp only [this, coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp,
    EquivLike.comp_injective]
  exact hf.lTensor_injective _

/-- Tensoring a pure map on the right with a module gives a pure map. -/
theorem IsPure.rTensor (hf : f.IsPure) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    (f.rTensor Q).IsPure := by
  rw [← comm_comp_lTensor_comp_comm_eq]
  exact ((TensorProduct.comm R Q N).isPure.comp (hf.lTensor Q)).comp
    (TensorProduct.comm R M Q).isPure

section BaseChange

variable (A : Type*) [CommRing A] [Algebra R A]

/-- **Purity is stable under base change**: if `f` is pure, then so is the `A`-linear map
`A ⊗[R] M → A ⊗[R] N`. -/
theorem IsPure.baseChange (hf : f.IsPure) : (f.baseChange A).IsPure := fun P _ _ ↦ by
  let _ : Module R P := Module.compHom P (algebraMap R A)
  have : IsScalarTower R A P := .of_algebraMap_smul fun _ _ ↦ rfl
  -- `P ⊗[A] (A ⊗[R] -)` is identified with `P ⊗[R] -` by `cancelBaseChange`.
  have key : (AlgebraTensorModule.cancelBaseChange R A A P N).toLinearMap ∘ₗ
      (f.baseChange A).lTensor P =
      AlgebraTensorModule.lTensor A P f ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R A A P M).toLinearMap := by
    ext
    simp
  have h := LinearMap.congr_fun key
  simp only [comp_apply, LinearEquiv.coe_coe, AlgebraTensorModule.coe_lTensor] at h
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange R A A P M).injective
  apply hf.lTensor_injective P
  rw [← h, ← h, hxy]

end BaseChange

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra R S] {M' N' : Type*} [AddCommGroup M'] [Module R M']
  [Module S M'] [IsScalarTower R S M'] [AddCommGroup N'] [Module R N'] [Module S N']
  [IsScalarTower R S N']

/-- **Purity is stable under restriction of scalars**: an `S`-linear map that is pure over `S`
is pure over `R`. -/
theorem IsPure.restrictScalars {f : M' →ₗ[S] N'} (hf : f.IsPure) :
    (f.restrictScalars R).IsPure := fun P _ _ ↦ by
  rw [lTensor_inj_iff_rTensor_inj]
  -- `- ⊗[S] (S ⊗[R] P)` is identified with `- ⊗[R] P` by `cancelBaseChange`.
  have key : ∀ x, (f.restrictScalars R).rTensor P
      (AlgebraTensorModule.cancelBaseChange R S S M' P x) =
      AlgebraTensorModule.cancelBaseChange R S S N' P (f.rTensor (S ⊗[R] P) x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m y =>
      induction y using TensorProduct.inductionOn with
      | tmul s p => simp
      | add y y' hy hy' => simp only [tmul_add, map_add, hy, hy']
    | add x x' hx hx' => simp only [map_add, hx, hx']
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange R S S M' P).symm.injective
  apply hf.rTensor_injective (S ⊗[R] P)
  apply (AlgebraTensorModule.cancelBaseChange R S S N' P).injective
  rw [← key, ← key]
  simpa using hxy

end RestrictScalars

section Flat

variable {P : Type*} [AddCommGroup P] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- **An injective map with flat cokernel is pure.** If `0 → M → N → P → 0` is exact and `P` is
flat, then `M → N` is pure. -/
theorem isPure_of_exact_of_flat [Module.Flat R P] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) : f.IsPure := fun _ _ _ ↦
  lTensor_injective_of_exact_of_flat g hg f hf hfg _

/-- **The cokernel of a pure map into a flat module is flat.** If `M → N → P → 0` is exact,
`M → N` is pure and `N` is flat, then `P` is flat. -/
theorem IsPure.flat_of_exact [Module.Flat R N] (hf : f.IsPure) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Module.Flat R P :=
  Module.Flat.of_exact_of_lTensor_quotient_injective f g hfg hg fun _ _ ↦
    hf.lTensor_injective _

/-- An injective map into a flat module is pure if and only if its cokernel is flat. -/
theorem isPure_iff_flat_of_exact [Module.Flat R N] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) : f.IsPure ↔ Module.Flat R P :=
  ⟨fun h ↦ h.flat_of_exact hfg hg, fun _ ↦ isPure_of_exact_of_flat hf hfg hg⟩

/-- **Flatness descends along pure maps.** If `M → N` is pure and `N` is flat, then `M` is flat:
for an ideal `I`, the map `M ⊗ I → M ⊗ R` followed by the injection `M ⊗ R → N ⊗ R` agrees with
the injection `M ⊗ I → N ⊗ I → N ⊗ R`. -/
theorem IsPure.flat_of_flat [Module.Flat R N] (hf : f.IsPure) : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  refine Function.Injective.of_comp (f := f.rTensor R) ?_
  rw [← coe_comp, rTensor_comp_lTensor, ← lTensor_comp_rTensor, coe_comp]
  exact (Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype).comp
    (hf.rTensor_injective I)

end Flat

end LinearMap

/-- A submodule of a flat module is pure, in the sense that its inclusion is a pure map, if and
only if the quotient is flat. -/
theorem Submodule.isPure_subtype_iff_flat {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] [Module.Flat R N] (M : Submodule R N) :
    M.subtype.IsPure ↔ Module.Flat R (N ⧸ M) :=
  LinearMap.isPure_iff_flat_of_exact M.injective_subtype (LinearMap.exact_subtype_mkQ M)
    M.mkQ_surjective

/-- An ideal `I` is pure in Mathlib's sense, that is `R ⧸ I` is flat, if and only if the inclusion
`I → R` is a pure map. -/
theorem Ideal.pure_iff_isPure_subtype {R : Type*} [CommRing R] (I : Ideal R) :
    I.Pure ↔ (Submodule.subtype I).IsPure :=
  (Submodule.isPure_subtype_iff_flat I).symm

/-- For a pure ideal `I`, the map `I ⊗[R] M → R ⊗[R] M` is injective for every module `M`: that is,
`Tor₁(R ⧸ I, M) = 0`. -/
theorem Ideal.subtype_rTensor_injective_of_pure {R : Type*} [CommRing R] (I : Ideal R) [I.Pure]
    (M : Type*) [AddCommGroup M] [Module R M] : Function.Injective (I.subtype.rTensor M) :=
  ((Ideal.pure_iff_isPure_subtype I).1 inferInstance).rTensor_injective M
