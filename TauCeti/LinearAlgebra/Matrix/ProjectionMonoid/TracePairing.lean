/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization

/-!
# Trace pairings on projection `K₀`-groups, unital and through the unitization

Let `R` be a star ring and `f : R →+ M` an additive map into an abelian group with
`f (a * b) = f (b * a)`, a *tracial* map. Its unnormalized matrix trace `f_m(p) = ∑ i, f (p i i)`
takes the same value on Murray–von Neumann equivalent matrix projections of any sizes and is
additive under block sum, so it induces the **trace pairing**
`f_* : K₀(R) →+ M` on the projection `K₀`-group (`TauCeti.ProjectionKZero.tracePairing`), natural
under star ring homomorphisms (`TauCeti.ProjectionKZero.tracePairing_comp_map`). Neither
positivity nor linearity enters.

For a nonunital star algebra `A` over a commutative star ring `K`, a tracial `f : A →+ M` and an
additive `g : K →+ M` on the scalars, `f⁺ (r, a) = g r + f a` is tracial on the forced
unitization `A⁺ = Unitization K A` (`TauCeti.UnitizationKZero.traceExtension`). Restricting its
trace
pairing to `K₀(A) = ker (K₀(A⁺) → K₀(K))` gives the pairing of `f` with the nonunital `K₀`-group
(`TauCeti.UnitizationKZero.tracePairing`). On a class `[e] − [p]` with `e` a projection over `A⁺`
whose scalar part is the projection `p` over `K`, it is `∑ i, f ((e i i).snd)`, the trace of
`e − p`, whose entries lie in `A` (`TauCeti.UnitizationKZero.tracePairing_of_mk_sub_of_mk`): the
values of `g` cancel. This is the nonunital trace pairing of OperatorKTheory K1.5, with
`τ⁺(a + λ) = τ(a) + λ`; it is natural for star homomorphisms
(`TauCeti.UnitizationKZero.tracePairing_comp_map`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

noncomputable section

open Matrix Algebra

namespace TauCeti

namespace ProjectionKZero

variable {R S M : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]
  [AddCommGroup M] {m : Type*} [Fintype m]

/-- The unnormalized matrix trace of a tracial additive map, as a function on `V(R)`. -/
private def traceFun (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) : ProjectionMonoid R → M :=
  ProjectionMonoid.lift (fun p _ ↦ ∑ i, f (p i i)) fun _ _ h ↦ h.sum_map_eq f hf

private theorem traceFun_mk (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) {p : Matrix m m R}
    (hp : IsStarProjection p) : traceFun f hf (ProjectionMonoid.mk p hp) = ∑ i, f (p i i) := by
  rw [traceFun, ProjectionMonoid.lift_mk_of_equiv _ _ hp (Fintype.equivFin m)]
  exact ((hp.isMurrayVonNeumannEquivalent_reindex _).sum_map_eq f hf).symm

/-- The unnormalized matrix trace on `V(R)`, as an additive monoid homomorphism. -/
private def traceMonoidHom (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    ProjectionMonoid R →+ M where
  toFun := traceFun f hf
  map_zero' := by
    rw [← ProjectionMonoid.mk_zero (m := Fin 0), traceFun_mk]
    simp
  map_add' x y := by
    induction x using ProjectionMonoid.ind with | mk k p hp => ?_
    induction y using ProjectionMonoid.ind with | mk l q hq => ?_
    rw [← ProjectionMonoid.mk_fromBlocks, traceFun_mk, traceFun_mk, traceFun_mk]
    simp [Fintype.sum_sum_type]

/-- The **trace pairing** `f_* : K₀(R) →+ M` of a tracial additive map `f : R →+ M`, induced by
the unnormalized matrix trace `f_m(p) = ∑ i, f (p i i)`. -/
def tracePairing (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) : ProjectionKZero R →+ M :=
  GrothendieckAddGroup.lift (traceMonoidHom f hf)

/-- The trace pairing sends the class of `p` to `∑ i, f (p i i)`. -/
theorem tracePairing_of_mk (f : R →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) {p : Matrix m m R}
    (hp : IsStarProjection p) :
    tracePairing f hf (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = ∑ i, f (p i i) :=
  (GrothendieckAddGroup.lift_apply_of _ _).trans (traceFun_mk f hf hp)

/-- **Naturality.** For a star ring homomorphism `φ : R → S` and a tracial `f : S →+ M`, the
pairing of `f ∘ φ` is the pairing of `f` composed with `φ_* : K₀(R) → K₀(S)`. -/
theorem tracePairing_comp_map (φ : R →⋆ₙ+* S) (f : S →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    tracePairing (f.comp φ.toNonUnitalRingHom.toAddMonoidHom)
        (fun a b ↦ by simpa using hf (φ a) (φ b)) =
      (tracePairing f hf).comp (map φ) := by
  refine GrothendieckAddGroup.addHom_ext fun x ↦ ?_
  induction x using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [AddMonoidHom.comp_apply, map_of_mk, tracePairing_of_mk, tracePairing_of_mk]
    simp

/-- The trace pairing depends only on the map `f`. -/
theorem tracePairing_congr {f f' : R →+ M} (h : f = f') (hf : ∀ a b, f (a * b) = f (b * a))
    (hf' : ∀ a b, f' (a * b) = f' (b * a)) : tracePairing f hf = tracePairing f' hf' := by
  subst h
  rfl

end ProjectionKZero

namespace UnitizationKZero

section traceExtension

variable {K A M : Type*} [CommSemiring K] [NonUnitalSemiring A] [AddCommGroup M]

/-- The extension `f⁺ (r, a) = g r + f a` of an additive map `f : A →+ M` to the unitization,
with value `g` on the scalars. -/
def traceExtension (g : K →+ M) (f : A →+ M) : _root_.Unitization K A →+ M where
  toFun x := g x.fst + f x.snd
  map_zero' := by simp
  map_add' x y := by
    simp only [_root_.Unitization.fst_add, _root_.Unitization.snd_add, map_add]
    abel

@[simp]
theorem traceExtension_apply (g : K →+ M) (f : A →+ M) (x : _root_.Unitization K A) :
    traceExtension g f x = g x.fst + f x.snd :=
  (rfl)

/-- The extension of a tracial map to the unitization is tracial. -/
theorem traceExtension_mul_comm [Module K A] (g : K →+ M) {f : A →+ M}
    (hf : ∀ a b, f (a * b) = f (b * a)) (x y : _root_.Unitization K A) :
    traceExtension g f (x * y) = traceExtension g f (y * x) := by
  simp only [traceExtension_apply, _root_.Unitization.fst_mul, _root_.Unitization.snd_mul,
    map_add, hf x.snd y.snd, mul_comm x.fst y.fst]
  abel

end traceExtension

variable {K A B M : Type*} [CommSemiring K] [StarRing K] [NonUnitalSemiring A] [StarRing A]
  [Module K A] [IsScalarTower K A A] [SMulCommClass K A A] [StarModule K A]
  [NonUnitalSemiring B] [StarRing B] [Module K B] [IsScalarTower K B B] [SMulCommClass K B B]
  [StarModule K B] [AddCommGroup M] {m : Type*} [Fintype m]

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
`f : A →+ M`: the trace pairing of `f⁺ (r, a) = g r + f a` on `K₀(A⁺)`, restricted to
`K₀(A) = ker (K₀(A⁺) → K₀(K))`. It does not depend on `g`
(`TauCeti.UnitizationKZero.tracePairing_of_mk_sub_of_mk`). -/
def tracePairing (g : K →+ M) (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    UnitizationKZero K A →+ M :=
  (ProjectionKZero.tracePairing (traceExtension g f)
    (traceExtension_mul_comm g hf)).comp (UnitizationKZero K A).subtype

/-- Unfolding `TauCeti.UnitizationKZero.tracePairing`. -/
theorem tracePairing_apply (g : K →+ M) (f : A →+ M) (hf : ∀ a b, f (a * b) = f (b * a))
    (x : UnitizationKZero K A) :
    tracePairing g f hf x =
      ProjectionKZero.tracePairing (traceExtension g f)
        (traceExtension_mul_comm g hf) x :=
  (rfl)

/-- On the scalar projections the extended trace pairing is the trace pairing of `g`. -/
theorem tracePairing_traceExtension_inl (g : K →+ M) (f : A →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) (x : ProjectionKZero K) :
    ProjectionKZero.tracePairing (traceExtension g f) (traceExtension_mul_comm g hf)
        (inl K A x) =
      ProjectionKZero.tracePairing g (fun a b ↦ by rw [mul_comm]) x := by
  rw [inl_def, ← AddMonoidHom.comp_apply, ← ProjectionKZero.tracePairing_comp_map]
  exact DFunLike.congr_fun (ProjectionKZero.tracePairing_congr
    (AddMonoidHom.ext fun r ↦ by simp [_root_.Unitization.algebraMap_eq_inl]) _ _) x

/-- **The pairing on a representative.** Let `e` be a projection over `A⁺` whose scalar part
`e.map fst` is the projection `p` over `K`. If `[e] − [p]` lies in `K₀(A)`, the trace pairing
sends it to `∑ i, f ((e i i).snd)`, the trace of `e − p`, whose entries lie in `A`. -/
theorem tracePairing_of_mk_sub_of_mk (g : K →+ M) (f : A →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) {e : Matrix m m (_root_.Unitization K A)}
    (he : IsStarProjection e) {p : Matrix m m K} (hp : IsStarProjection p)
    (hep : e.map (fun x ↦ x.fst) = p)
    (hx : GrothendieckAddGroup.of (ProjectionMonoid.mk e he) -
      inl K A (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) ∈ UnitizationKZero K A) :
    tracePairing g f hf ⟨_, hx⟩ = ∑ i, f ((e i i).snd) := by
  rw [tracePairing_apply, map_sub, tracePairing_traceExtension_inl g f hf,
    ProjectionKZero.tracePairing_of_mk, ProjectionKZero.tracePairing_of_mk, ← hep]
  simp [Finset.sum_add_distrib]

/-- **Naturality.** For a star homomorphism `φ : A → B` and a tracial `f : B →+ M`, the pairing of
`f ∘ φ` is the pairing of `f` composed with `φ_* : K₀(A) → K₀(B)`. -/
theorem tracePairing_comp_map (φ : A →⋆ₙₐ[K] B) (g : K →+ M) (f : B →+ M)
    (hf : ∀ a b, f (a * b) = f (b * a)) :
    tracePairing g (f.comp φ.toNonUnitalAlgHom.toAddMonoidHom)
        (fun a b ↦ by simpa using hf (φ a) (φ b)) =
      (tracePairing g f hf).comp (map φ) := by
  have h : traceExtension g (f.comp φ.toNonUnitalAlgHom.toAddMonoidHom) =
      (traceExtension g f).comp (NonUnitalStarRingHom.ofClass
        (_root_.Unitization.starMap φ)).toNonUnitalRingHom.toAddMonoidHom :=
    AddMonoidHom.ext fun x ↦ by simp
  ext x
  rw [AddMonoidHom.comp_apply, tracePairing_apply, tracePairing_apply, coe_map,
    ← AddMonoidHom.comp_apply, ← ProjectionKZero.tracePairing_comp_map]
  exact congrArg (· (x : ProjectionKZero _)) (ProjectionKZero.tracePairing_congr h _ _)

end UnitizationKZero

end TauCeti
