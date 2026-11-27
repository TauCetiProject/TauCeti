/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.TracePairing
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.Basic

/-!
# Trace pairings on the nonunital `K₀`-group, through the unitization

For a nonunital star algebra `A` over a commutative star ring `K`, a tracial `f : A →+ M` and an
additive `g : K →+ M` on the scalars, `f⁺ (r, a) = g r + f a` is tracial on the forced
unitization `A⁺ = Unitization K A` (`Unitization.traceExtension`). Restricting its trace
pairing (`TauCeti.ProjectionKZero.tracePairing`) to `K₀(A) = ker (K₀(A⁺) → K₀(K))` gives
the pairing of `f` with the nonunital `K₀`-group (`TauCeti.UnitizationKZero.tracePairing`), which
does not depend on `g` (`TauCeti.UnitizationKZero.tracePairing_traceExtension`): the `g`-part of
the pairing factors through `K₀(A⁺) → K₀(K)`
(`TauCeti.ProjectionKZero.tracePairing_traceExtension_eq_add`), which vanishes on `K₀(A)`. For
`τ⁺(a + λ) = τ(a) + λ` take `g = id`.

On a class `[e] − [p]` with `e` a projection over `A⁺` and `p` a projection over `K`, the pairing
is `∑ i, f ((e i i).snd)` (`TauCeti.UnitizationKZero.tracePairing_of_mk_sub_inl_of_mk`); when `p`
is the scalar part of `e`, this is the trace of `e − p`, whose entries lie in `A`. The pairing is
natural for star homomorphisms (`TauCeti.UnitizationKZero.tracePairing_comp_map`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

noncomputable section

open Matrix Algebra

namespace TauCeti

variable {K A B M : Type*} [CommSemiring K] [StarRing K] [NonUnitalSemiring A] [StarRing A]
  [Module K A] [IsScalarTower K A A] [SMulCommClass K A A] [StarModule K A]
  [NonUnitalSemiring B] [StarRing B] [Module K B] [IsScalarTower K B B] [SMulCommClass K B B]
  [StarModule K B] [AddCommGroup M] {m : Type*} [Fintype m]

namespace ProjectionKZero

/-- **The scalar part of an extended trace pairing.** The trace pairing of
`f⁺ (r, a) = g r + f a` on `K₀(A⁺)` is that of `(r, a) ↦ f a` plus the pairing of `g` on `K₀(K)`
composed with the augmentation `K₀(A⁺) → K₀(K)`. -/
theorem tracePairing_traceExtension_eq_add (g : K →+ M) (f : A →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) :
    tracePairing (Unitization.traceExtension g f) (Unitization.traceExtension_mul_comm g hf) =
      tracePairing (Unitization.traceExtension 0 f) (Unitization.traceExtension_mul_comm 0 hf) +
        (tracePairing g fun a b ↦ by rw [mul_comm]).comp (UnitizationKZero.augmentation K A) := by
  refine GrothendieckAddGroup.addHom_ext fun y ↦ ?_
  induction y using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, UnitizationKZero.augmentation_def,
      map_of_mk, tracePairing_of_mk, tracePairing_of_mk, tracePairing_of_mk]
    simp [Finset.sum_add_distrib, add_comm]

end ProjectionKZero

namespace UnitizationKZero

/-- A projection `e` over `A⁺` with scalar part the projection `p` over `K` gives the class
`[e] − [p]` of `K₀(A)`. -/
theorem of_mk_sub_inl_of_mk_mem {e : Matrix m m (_root_.Unitization K A)}
    (he : IsStarProjection e) {p : Matrix m m K} (hp : IsStarProjection p)
    (hep : e.map (fun x ↦ x.fst) = p) :
    GrothendieckAddGroup.of (ProjectionMonoid.mk e he) -
      inl K A (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) ∈ UnitizationKZero K A := by
  subst hep
  rw [mem_iff, map_sub, augmentation_inl, augmentation_def, ProjectionKZero.map_of_mk, sub_eq_zero]
  congr 2
  exact Matrix.ext fun i j ↦ by simp

/-- The **trace pairing of the nonunital `K₀`-group** `K₀(A) →+ M` of a tracial additive map
`f : A →+ M`: the trace pairing of `f⁺ (r, a) = f a` on `K₀(A⁺)`, restricted to
`K₀(A) = ker (K₀(A⁺) → K₀(K))`. Any other value on the scalars gives the same pairing
(`TauCeti.UnitizationKZero.tracePairing_traceExtension`). -/
def tracePairing (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    UnitizationKZero K A →+ M :=
  (ProjectionKZero.tracePairing (Unitization.traceExtension 0 f)
    (Unitization.traceExtension_mul_comm 0 hf)).comp (UnitizationKZero K A).subtype

/-- Unfolding `TauCeti.UnitizationKZero.tracePairing`. -/
theorem tracePairing_apply (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    (x : UnitizationKZero K A) :
    tracePairing f hf x =
      ProjectionKZero.tracePairing (Unitization.traceExtension 0 f)
        (Unitization.traceExtension_mul_comm 0 hf) (x : ProjectionKZero (_root_.Unitization K A)) :=
  (rfl)

/-- The nonunital trace pairing depends only on the map `f`. -/
theorem tracePairing_congr {f f' : A →+ M} (h : f = f') (hf : ∀ a b, f (a * b) = f (b * a))
    (hf' : ∀ a b, f' (a * b) = f' (b * a)) :
    tracePairing (K := K) f hf = tracePairing f' hf' := by
  subst h
  rfl

/-- **Independence of the scalar values.** For any `g : K →+ M`, the trace pairing of
`f⁺ (r, a) = g r + f a` restricts on `K₀(A)` to the nonunital trace pairing of `f`. -/
theorem tracePairing_traceExtension (g : K →+ M) (f : A →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) (x : UnitizationKZero K A) :
    ProjectionKZero.tracePairing (Unitization.traceExtension g f)
        (Unitization.traceExtension_mul_comm g hf) (x : ProjectionKZero (_root_.Unitization K A)) =
      tracePairing f hf x := by
  rw [ProjectionKZero.tracePairing_traceExtension_eq_add g f hf, AddMonoidHom.add_apply,
    AddMonoidHom.comp_apply, (mem_iff _).1 x.property, _root_.map_zero, add_zero,
    tracePairing_apply]

/-- **The pairing on a representative.** Let `e` be a projection over `A⁺` and `p` a projection
over `K`. If `[e] − [p]` lies in `K₀(A)`, the trace pairing sends it to `∑ i, f ((e i i).snd)`.
When `p` is the scalar part of `e` (`TauCeti.UnitizationKZero.of_mk_sub_inl_of_mk_mem`), this is
the trace of `e − p`, whose entries lie in `A`. -/
theorem tracePairing_of_mk_sub_inl_of_mk (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    {e : Matrix m m (_root_.Unitization K A)} (he : IsStarProjection e) {p : Matrix m m K}
    (hp : IsStarProjection p)
    (hx : GrothendieckAddGroup.of (ProjectionMonoid.mk e he) -
      inl K A (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) ∈ UnitizationKZero K A) :
    tracePairing f hf ⟨_, hx⟩ = ∑ i, f ((e i i).snd) := by
  rw [tracePairing_apply, map_sub, inl_def, ProjectionKZero.map_of_mk,
    ProjectionKZero.tracePairing_of_mk, ProjectionKZero.tracePairing_of_mk]
  simp [_root_.Unitization.algebraMap_eq_inl]

/-- **Naturality.** For a star homomorphism `φ : A → B` and a tracial `f : B →+ M`, the pairing of
`f ∘ φ` is the pairing of `f` composed with `φ_* : K₀(A) → K₀(B)`. -/
theorem tracePairing_comp_map (φ : A →⋆ₙₐ[K] B) (f : B →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) :
    tracePairing (f.comp φ.toNonUnitalAlgHom.toAddMonoidHom)
        (fun a b ↦ by simpa using hf (φ a) (φ b)) =
      (tracePairing f hf).comp (map φ) := by
  have h : Unitization.traceExtension (0 : K →+ M) (f.comp φ.toNonUnitalAlgHom.toAddMonoidHom) =
      (Unitization.traceExtension 0 f).comp (NonUnitalStarRingHom.ofClass
        (_root_.Unitization.starMap φ)).toNonUnitalRingHom.toAddMonoidHom :=
    AddMonoidHom.ext fun x ↦ by simp
  ext x
  rw [AddMonoidHom.comp_apply, tracePairing_apply, tracePairing_apply, coe_map,
    ← AddMonoidHom.comp_apply, ← ProjectionKZero.tracePairing_comp_map]
  exact congrArg (· (x : ProjectionKZero _)) (ProjectionKZero.tracePairing_congr h _ _)

end UnitizationKZero

end TauCeti
