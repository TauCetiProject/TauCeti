/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Descent of continuous group homomorphisms

A continuous group homomorphism descends through a quotient map precisely when its kernel contains
the kernel of the quotient homomorphism. The construction uses
`TauCeti.ContinuousMonoidHom.quotientLift` on the kernel quotient and Mathlib's
`QuotientGroup.quotientKerEquivOfSurjective` to identify that quotient with the target. The
quotient-map hypothesis ensures that the descended homomorphism is continuous.

## Main results

* `ContinuousMonoidHom.liftOfIsQuotientMap` descends a continuous homomorphism through a quotient
  homomorphism.
* `ContinuousMonoidHom.homEquivOfIsQuotientMap` identifies continuous homomorphisms out of the
  quotient with continuous homomorphisms upstairs that kill the quotient kernel.
-/

public section

open Topology

namespace ContinuousMonoidHom

variable {G Q H : Type*} [Group G] [Group Q] [Monoid H]
  [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace H]

private noncomputable def liftMonoidHomOfIsQuotientMap (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker) : Q →* H :=
  let e := QuotientGroup.quotientKerEquivOfSurjective (p : G →* Q) hp.surjective
  let lift := TauCeti.ContinuousMonoidHom.quotientLift (p : G →* Q).ker f hf
  lift.toMonoidHom.comp e.symm.toMonoidHom

private theorem liftMonoidHomOfIsQuotientMap_comp_apply (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker) (x : G) :
    liftMonoidHomOfIsQuotientMap p hp f hf (p x) = f x := by
  have hx :
      (QuotientGroup.quotientKerEquivOfSurjective (p : G →* Q)
        hp.surjective).symm.toMonoidHom (p x) = (x : G ⧸ (p : G →* Q).ker) :=
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply
      (p : G →* Q) hp.surjective x
  rw [liftMonoidHomOfIsQuotientMap, MonoidHom.comp_apply, hx]
  exact TauCeti.ContinuousMonoidHom.quotientLift_mk (p : G →* Q).ker f hf x

/-- Descend a continuous group homomorphism through a quotient homomorphism whose kernel it
kills. -/
noncomputable def liftOfIsQuotientMap (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker) : Q →ₜ* H where
  toMonoidHom := liftMonoidHomOfIsQuotientMap p hp f hf
  continuous_toFun := hp.continuous_iff.mpr <| f.continuous.congr fun x ↦
    (liftMonoidHomOfIsQuotientMap_comp_apply p hp f hf x).symm

/-- The descended continuous homomorphism agrees with the original homomorphism on every
representative. -/
@[simp]
theorem liftOfIsQuotientMap_comp_apply (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker) (x : G) :
    liftOfIsQuotientMap p hp f hf (p x) = f x := by
  exact liftMonoidHomOfIsQuotientMap_comp_apply p hp f hf x

/-- Composing the descended homomorphism with the quotient homomorphism recovers the original
homomorphism. -/
@[simp]
theorem liftOfIsQuotientMap_comp (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker) :
    (liftOfIsQuotientMap p hp f hf).comp p = f := by
  ext x
  exact liftOfIsQuotientMap_comp_apply p hp f hf x

/-- A continuous homomorphism descended through a quotient homomorphism is uniquely determined by
its composition with that quotient homomorphism. -/
theorem liftOfIsQuotientMap_unique (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : G →ₜ* H) (hf : (p : G →* Q).ker ≤ (f : G →* H).ker)
    (g : Q →ₜ* H) (hg : g.comp p = f) : g = liftOfIsQuotientMap p hp f hf := by
  ext y
  obtain ⟨x, rfl⟩ := hp.surjective y
  rw [liftOfIsQuotientMap_comp_apply]
  exact DFunLike.congr_fun hg x

/-- Precomposition with a quotient homomorphism identifies continuous homomorphisms on the
quotient with continuous homomorphisms whose kernels contain the quotient kernel. -/
noncomputable def homEquivOfIsQuotientMap (p : G →ₜ* Q) (hp : IsQuotientMap p) :
    (Q →ₜ* H) ≃ {f : G →ₜ* H // (p : G →* Q).ker ≤ (f : G →* H).ker} :=
  let forward : (Q →ₜ* H) →
      {f : G →ₜ* H // (p : G →* Q).ker ≤ (f : G →* H).ker} := fun f ↦
    ⟨f.comp p, by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      exact (congrArg f hx).trans (map_one f)⟩
  {
  toFun := forward
  invFun f := liftOfIsQuotientMap p hp f.1 f.2
  left_inv f :=
    (liftOfIsQuotientMap_unique p hp (forward f).1 (forward f).2 f rfl).symm
  right_inv f := by
    apply Subtype.ext
    exact liftOfIsQuotientMap_comp p hp f.1 f.2
  }

/-- Evaluation of the forward quotient-homomorphism equivalence. -/
@[simp]
theorem homEquivOfIsQuotientMap_apply_coe (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : Q →ₜ* H) :
    ((homEquivOfIsQuotientMap p hp f :
      {g : G →ₜ* H // (p : G →* Q).ker ≤ (g : G →* H).ker}) : G →ₜ* H) =
      f.comp p := by
  rw [homEquivOfIsQuotientMap]
  rfl

/-- Evaluation of the inverse quotient-homomorphism equivalence. -/
@[simp]
theorem homEquivOfIsQuotientMap_symm_apply (p : G →ₜ* Q) (hp : IsQuotientMap p)
    (f : {g : G →ₜ* H // (p : G →* Q).ker ≤ (g : G →* H).ker}) :
    (homEquivOfIsQuotientMap p hp).symm f = liftOfIsQuotientMap p hp f.1 f.2 := by
  apply (homEquivOfIsQuotientMap p hp).injective
  rw [(homEquivOfIsQuotientMap p hp).apply_symm_apply]
  apply Subtype.ext
  rw [homEquivOfIsQuotientMap_apply_coe, liftOfIsQuotientMap_comp]

end ContinuousMonoidHom
