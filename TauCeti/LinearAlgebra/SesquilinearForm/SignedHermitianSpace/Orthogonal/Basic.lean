/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Dual
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry

/-!
# Orthogonal complements of nondegenerate subspaces

Let `(V, h)` be a signed hermitian space over a field with involution `σ`, of any dimension, and
let `W` be a finite-dimensional subspace on which `h` stays nondegenerate. Then `V` is the direct
sum of `W` and its orthogonal `Wᗮ = {v | ∀ w ∈ W, h w v = 0}`, the form stays nondegenerate on
`Wᗮ`, and `(V, h)` is isometric to the orthogonal sum `W ⊥ Wᗮ` of the two restrictions. This is
how hyperbolic planes and anisotropic vectors are split off a hermitian space.

The decomposition `v = w + (v - w)` takes for `w` the vector of `W` representing the functional
`h v ·` on `W`, which exists because `h` identifies the finite-dimensional `W` with its dual
(`TauCeti.SignedHermitianSpace.form_bijective`).

## Main statements

* `TauCeti.SignedHermitianSpace.isCompl_orthogonalBilin`: `V = W ⊕ Wᗮ`.
* `TauCeti.SignedHermitianSpace.separatingLeft_domRestrict_orthogonalBilin`: `h` is nondegenerate
  on `Wᗮ`.
* `TauCeti.SignedHermitianSpace.equivalent_restrict_prod_orthogonalBilin`: `V ≅ W ⊥ Wᗮ`.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}
  (H : SignedHermitianSpace K V σ ε) {W : Submodule K V}

/-- **Orthogonal complement of a nondegenerate subspace.** If the form of a signed hermitian space
`V` stays nondegenerate on a finite-dimensional subspace `W`, then `V = W ⊕ Wᗮ`. -/
theorem isCompl_orthogonalBilin [RingHomSurjective σ] [FiniteDimensional K W]
    (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft) :
    IsCompl W (W.orthogonalBilin H.form) := by
  refine ⟨(H.separatingLeft_domRestrict_iff W).1 hW, codisjoint_iff.2 ?_⟩
  refine Submodule.eq_top_iff'.2 fun v ↦ ?_
  -- The vector `w` of `W` representing `h v ·` on `W` leaves `v - w` orthogonal to `W`.
  obtain ⟨w, hw⟩ := (H.restrict W hW).form_bijective.2 (H.form v ∘ₗ W.subtype)
  have hvw : v - w ∈ W.orthogonalBilin H.form := Submodule.mem_orthogonalBilin.2 fun u hu ↦
    H.isRefl _ _ <| by
      have := LinearMap.congr_fun hw ⟨u, hu⟩
      simp only [restrict_form_apply, LinearMap.comp_apply, Submodule.coe_subtype] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self]
  simpa using Submodule.add_mem_sup w.property hvw

/-- If the form of a signed hermitian space stays nondegenerate on a finite-dimensional subspace
`W`, it also stays nondegenerate on the orthogonal `Wᗮ`. -/
theorem separatingLeft_domRestrict_orthogonalBilin [RingHomSurjective σ] [FiniteDimensional K W]
    (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft) :
    (H.form.domRestrict₁₂ (W.orthogonalBilin H.form)
      (W.orthogonalBilin H.form)).SeparatingLeft := by
  rw [separatingLeft_domRestrict_iff, Submodule.disjoint_def]
  intro x hx hx'
  -- `x` is orthogonal to `W` and to `Wᗮ`, hence to `W ⊔ Wᗮ = V`.
  refine H.separatingLeft x fun v ↦ ?_
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1
    ((H.isCompl_orthogonalBilin hW).sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, H.isRefl _ _ ((Submodule.mem_orthogonalBilin.1 hx) w hw),
    H.isRefl _ _ ((Submodule.mem_orthogonalBilin.1 hx') u hu), add_zero]

/-- **Orthogonal splitting.** If the form of a signed hermitian space `V` stays nondegenerate on a
finite-dimensional subspace `W`, then `V` is isometric to the orthogonal sum `W ⊥ Wᗮ`. -/
theorem equivalent_restrict_prod_orthogonalBilin [RingHomSurjective σ] [FiniteDimensional K W]
    (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft) :
    Equivalent H ((H.restrict W hW).prod (H.restrict (W.orthogonalBilin H.form)
      (H.separatingLeft_domRestrict_orthogonalBilin hW))) := by
  have hc := H.isCompl_orthogonalBilin hW
  refine Equivalent.symm <| IsometryEquiv.equivalent
    { Submodule.prodEquivOfIsCompl _ _ hc with map_app' := fun x y ↦ ?_ }
  have h₁ := (Submodule.mem_orthogonalBilin.1 y.2.property) x.1 x.1.property
  have h₂ := H.isRefl _ _ ((Submodule.mem_orthogonalBilin.1 x.2.property) y.1 y.1.property)
  simp [h₁, h₂]

end SignedHermitianSpace

end TauCeti
