/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Unitary
public import TauCeti.RingTheory.CentralIdempotent
import TauCeti.Algebra.MonoidAlgebra.Center
import TauCeti.Algebra.MonoidAlgebra.PositiveInvolution
import TauCeti.RepresentationTheory.Intertwining.Semilinear

/-!
# Central idempotents and transported inner products

Central idempotents of the real or complex group algebra act by orthogonal projections in
unitary representations. The same symmetry holds for a pairing transported through a
semilinear intertwiner: the coefficient map preserves central idempotents even when it
does not preserve complex conjugation.

The transported pairing is the group-algebra part of `New.DescentPair.innerAt_groupAlgAction`
in `grh/src/New/OneLift/TestedForms.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/OneLift/TestedForms.lean
-/

public section

open TauCeti
open scoped InnerProductSpace

namespace Representation

/-- In a unitary representation, a central idempotent acts by a symmetric idempotent operator.
No finiteness assumption on the group or the representation is needed. -/
theorem isSymmetricProjection_asAlgebraHom_of_mem_centralIdempotents
    {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (ρ : Representation 𝕜 G V) (hρ : ∀ g v w, ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {e : MonoidAlgebra 𝕜 G} (he : e ∈ centralIdempotents (MonoidAlgebra 𝕜 G)) :
    (ρ.asAlgebraHom e).IsSymmetricProjection := by
  refine ρ.isSymmetricProjection_asAlgebraHom hρ (fun g ↦ ?_)
    (isIdempotentElem_of_mem_centralIdempotents he)
  have h := congrArg (fun a : MonoidAlgebra 𝕜 G ↦ a.coeff g⁻¹)
    (star_eq_self_of_mem_centralIdempotents he)
  simpa only [MonoidAlgebra.coeff_star, inv_inv] using h.symm

/-- A central idempotent is symmetric for the pairing pulled back along a semilinear
intertwiner into a unitary representation. If the scalar map is an isomorphism, applying its
inverse to both sides gives the same equality for the conjugated sesquilinear pairing. -/
theorem inner_map_asAlgebraHom_eq_of_mem_centralIdempotents
    {R 𝕜 G V W : Type*} [CommRing R] [RCLike 𝕜] [Group G] [AddCommMonoid V] [Module R V]
    [SeminormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (ρ : Representation R G V) {τ : Representation 𝕜 G W} {σ : R →+* 𝕜}
    (f : V →ₛₗ[σ] W) (hf : ∀ g v, f (ρ g v) = τ g (f v))
    (hτ : ∀ g v w, ⟪τ g v, τ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {e : MonoidAlgebra R G} (he : e ∈ centralIdempotents (MonoidAlgebra R G)) (v w : V) :
    ⟪f (ρ.asAlgebraHom e v), f w⟫_𝕜 = ⟪f v, f (ρ.asAlgebraHom e w)⟫_𝕜 := by
  have hc := mem_centralIdempotents.mp he
  have hc' : e ∈ Subalgebra.center R (MonoidAlgebra R G) :=
    Subalgebra.mem_center_iff.mpr (Subring.mem_center_iff.mp hc.2)
  have hmap : MonoidAlgebra.mapRingHom G σ e ∈ centralIdempotents (MonoidAlgebra 𝕜 G) :=
    mem_centralIdempotents.mpr ⟨hc.1.map _, Subring.mem_center_iff.mpr
      (Subalgebra.mem_center_iff.mp (MonoidAlgebra.mapRingHom_mem_center G σ hc'))⟩
  simp only [f.map_asAlgebraHom_apply_of_intertwines hf]
  exact (τ.isSymmetricProjection_asAlgebraHom_of_mem_centralIdempotents hτ hmap).isSymmetric
    (f v) (f w)

end Representation
