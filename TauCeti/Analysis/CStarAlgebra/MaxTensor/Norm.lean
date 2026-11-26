/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
public import TauCeti.Analysis.CStarAlgebra.Representation.GNS
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The maximal C*-norm on an algebraic tensor product of C*-algebras

Let `A` and `B` be (possibly non-unital) C*-algebras. A **commuting pair of representations**
of `A` and `B` (`TauCeti.CommutingRepresentationPair A B`) is a Hilbert space `H` with star
homomorphisms `π : A → B(H)` and `ρ : B → B(H)` whose ranges commute. Such a pair integrates to
the star homomorphism `A ⊗[ℂ] B → B(H)`, `a ⊗ b ↦ π a * ρ b`
(`TauCeti.CommutingRepresentationPair.tensorHom`). The **maximal norm** of `x : A ⊗[ℂ] B` is
the supremum of `‖(π × ρ) x‖` over all commuting pairs (`TauCeti.maxTensorNorm`). The Hilbert
spaces range over the universe `max u v` when `A : Type u` and `B : Type v`; this universe
contains the Hilbert tensor product of faithful representations of `A` and `B`, which is what
makes the supremum a norm. A **pair of representations** (`TauCeti.RepresentationPair A B`) is
a pair `π : A → B(E)`, `ρ : B → B(F)` on Hilbert spaces in the universes of `A` and `B`; its
spatial pair `a ↦ π a ⊗ 1`, `b ↦ 1 ⊗ ρ b` on `E ⊗₂ F` is a commuting pair.

The norm properties hold for the supremum `TauCeti.supTensorNorm f` of `‖(f i).tensorHom x‖` over
any family `f` of commuting pairs, and the maximal norm is the case of all commuting pairs. The
minimal norm `TauCeti.minTensorNorm` is the case of the spatial pairs.

The supremum is finite: a star homomorphism between C*-algebras is contractive, so
`‖(π × ρ)(Σ aᵢ ⊗ bᵢ)‖ ≤ Σ ‖aᵢ‖ ‖bᵢ‖` (`TauCeti.maxTensorNorm_le_sum`). The maximal norm is a
submultiplicative star norm with the C*-identity `‖x⋆ x‖_max = ‖x‖_max ^ 2`
(`TauCeti.maxTensorNorm_star_mul_self`), and a cross norm, `‖a ⊗ b‖_max = ‖a‖ ‖b‖`
(`TauCeti.maxTensorNorm_tmul`). It vanishes only at `0`
(`TauCeti.maxTensorNorm_eq_zero_iff`): faithful representations `A ⊆ B(E)` and `B ⊆ B(F)`
(Gelfand–Naimark) give the commuting pair `a ⊗ 1`, `1 ⊗ b` on `E ⊗₂ F`, whose integrated form is
the injective spatial tensor homomorphism `NonUnitalStarAlgHom.spatialTensorHom` of the two
representations (`TauCeti.CommutingRepresentationPair.tensorHom_spatial_injective`).

The maximal norm dominates every norm obtained from a commuting pair in the universe `max u v`
(`TauCeti.norm_tensorHom_le_maxTensorNorm`), every norm obtained from commuting star homomorphisms
into a C*-algebra in that universe (`TauCeti.norm_liftNonUnitalStarAlgHom_le_maxTensorNorm`), and
the supremum over any family of commuting pairs (`TauCeti.supTensorNorm_le_maxTensorNorm`).

## Main declarations

* `TauCeti.CommutingRepresentationPair A B`: commuting pairs of representations, with
  `TauCeti.CommutingRepresentationPair.tensorHom` and the spatial pair
  `TauCeti.CommutingRepresentationPair.spatial`.
* `TauCeti.RepresentationPair A B`: pairs of representations, with the spatial commuting pair
  `TauCeti.RepresentationPair.spatial`.
* `TauCeti.supTensorNorm f`: the supremum of the norms of a family of commuting pairs.
* `TauCeti.maxTensorNorm A B`: the maximal C*-norm on `A ⊗[ℂ] B`.

The completion `A ⊗max B`, its universal property, the comparison of an arbitrary C*-norm with
the minimal and maximal norms and the functoriality of `A ⊗max B` are not in this file.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3.
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A **commuting pair of representations** of `A` and `B`: a complex Hilbert space `H` in the
universe `max u v` with star homomorphisms `left : A → B(H)` and `right : B → B(H)` whose ranges
commute. -/
structure CommutingRepresentationPair where
  /-- The Hilbert space. -/
  H : Type (max u v)
  /-- The norm of the Hilbert space. -/
  [instNormedAddCommGroup : NormedAddCommGroup H]
  /-- The inner product of the Hilbert space. -/
  [instInnerProductSpace : InnerProductSpace ℂ H]
  /-- The Hilbert space is complete. -/
  [instCompleteSpace : CompleteSpace H]
  /-- The representation of `A`. -/
  left : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- The representation of `B`. -/
  right : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- The two representations commute. -/
  commute (a : A) (b : B) : Commute (left a) (right b)

attribute [instance] CommutingRepresentationPair.instNormedAddCommGroup
  CommutingRepresentationPair.instInnerProductSpace CommutingRepresentationPair.instCompleteSpace

namespace CommutingRepresentationPair

variable {A B}

/-- The integrated form `A ⊗[ℂ] B → B(H)`, `a ⊗ b ↦ π a * ρ b`, of a commuting pair. -/
def tensorHom (p : CommutingRepresentationPair A B) :
    A ⊗[ℂ] B →⋆ₙₐ[ℂ] (p.H →L[ℂ] p.H) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom p.left p.right p.commute

/-- Unfolding `TauCeti.CommutingRepresentationPair.tensorHom`. -/
theorem tensorHom_def (p : CommutingRepresentationPair A B) :
    p.tensorHom = Algebra.TensorProduct.liftNonUnitalStarAlgHom p.left p.right p.commute :=
  (rfl)

@[simp]
theorem tensorHom_tmul (p : CommutingRepresentationPair A B) (a : A) (b : B) :
    p.tensorHom (a ⊗ₜ b) = p.left a * p.right b :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul _ _ _

/-- The integrated form of a commuting pair is bounded by `Σ ‖aᵢ‖ ‖bᵢ‖` on `Σ aᵢ ⊗ bᵢ`. -/
theorem norm_tensorHom_sum_le (p : CommutingRepresentationPair A B) {ι : Type*} (s : Finset ι)
    (a : ι → A) (b : ι → B) :
    ‖p.tensorHom (∑ i ∈ s, a i ⊗ₜ b i)‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [tensorHom_tmul]
  exact (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le _ _)
    (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _) (norm_nonneg _))

/-- For each `x`, the norms `‖(π × ρ) x‖` over all commuting pairs are bounded. -/
theorem bddAbove_range_norm_tensorHom (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun p : CommutingRepresentationPair A B ↦ ‖p.tensorHom x‖) := by
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  exact ⟨∑ i ∈ S, ‖i.1‖ * ‖i.2‖, by
    rintro _ ⟨p, rfl⟩
    exact p.norm_tensorHom_sum_le S Prod.fst Prod.snd⟩

section Spatial

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **spatial pair** of representations `π : A → B(E)` and `ρ : B → B(F)`: the commuting
amplifications `a ↦ π a ⊗ 1` and `b ↦ 1 ⊗ ρ b` on the Hilbert tensor product `E ⊗₂ F`.

It is an abbreviation so that `simp` and instance search see its Hilbert space as
`Completion (E ⊗[ℂ] F)` with its own instances, and so can apply the lemmas about operators on
that space (such as `NonUnitalStarAlgHom.spatialTensorHom_tmul`) to its operators. -/
abbrev spatial (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    CommutingRepresentationPair A B where
  H := Completion (E ⊗[ℂ] F)
  left := π.rTensorCompletion F
  right := ρ.lTensorCompletion E
  commute := π.commute_rTensorCompletion_lTensorCompletion ρ

/-- The left representation of the spatial pair is `a ↦ π a ⊗ 1`. -/
theorem spatial_left_apply (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (a : A) :
    (spatial π ρ).left a = (π a).rTensorCompletion F :=
  π.rTensorCompletion_apply a

/-- The right representation of the spatial pair is `b ↦ 1 ⊗ ρ b`. -/
theorem spatial_right_apply (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) (b : B) :
    (spatial π ρ).right b = (ρ b).lTensorCompletion E :=
  ρ.lTensorCompletion_apply b

/-- The integrated form of the spatial pair is the spatial tensor homomorphism of `π` and `ρ`:
both are `Algebra.TensorProduct.liftNonUnitalStarAlgHom` of the same two amplifications. -/
@[simp]
theorem tensorHom_spatial (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    (spatial π ρ).tensorHom = π.spatialTensorHom ρ := by
  rw [tensorHom_def, NonUnitalStarAlgHom.spatialTensorHom_def]

/-- The integrated form of the spatial pair sends `a ⊗ b` to `π a ⊗ ρ b`. -/
theorem tensorHom_spatial_tmul (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (a : A) (b : B) :
    (spatial π ρ).tensorHom (a ⊗ₜ b) = mapLCompletion (π a) (ρ b) :=
  (DFunLike.congr_fun (tensorHom_spatial π ρ) (a ⊗ₜ b)).trans
    (NonUnitalStarAlgHom.spatialTensorHom_tmul π ρ a b)

/-- The integrated form of the spatial pair has norm `‖π a‖ ‖ρ b‖` at `a ⊗ b`. -/
theorem norm_tensorHom_spatial_tmul (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (a : A) (b : B) : ‖(spatial π ρ).tensorHom (a ⊗ₜ b)‖ = ‖π a‖ * ‖ρ b‖ := by
  rw [tensorHom_spatial_tmul]
  exact norm_mapLCompletion _ _

/-- For faithful representations, the integrated form of the spatial pair is injective. -/
theorem tensorHom_spatial_injective {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) :
    Function.Injective (spatial π ρ).tensorHom := by
  rw [tensorHom_spatial]
  exact NonUnitalStarAlgHom.spatialTensorHom_injective hπ hρ

end Spatial

end CommutingRepresentationPair

/-- A **pair of representations** of `A` and `B`: star homomorphisms `left : A → B(E)` and
`right : B → B(F)` on complex Hilbert spaces `E` and `F` in the universes of `A` and `B`. -/
structure RepresentationPair where
  /-- The Hilbert space of the representation of `A`. -/
  E : Type u
  /-- The Hilbert space of the representation of `B`. -/
  F : Type v
  /-- The norm of `E`. -/
  [instNormedAddCommGroupE : NormedAddCommGroup E]
  /-- The inner product of `E`. -/
  [instInnerProductSpaceE : InnerProductSpace ℂ E]
  /-- `E` is complete. -/
  [instCompleteSpaceE : CompleteSpace E]
  /-- The norm of `F`. -/
  [instNormedAddCommGroupF : NormedAddCommGroup F]
  /-- The inner product of `F`. -/
  [instInnerProductSpaceF : InnerProductSpace ℂ F]
  /-- `F` is complete. -/
  [instCompleteSpaceF : CompleteSpace F]
  /-- The representation of `A`. -/
  left : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)
  /-- The representation of `B`. -/
  right : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)

attribute [instance] RepresentationPair.instNormedAddCommGroupE
  RepresentationPair.instInnerProductSpaceE RepresentationPair.instCompleteSpaceE
  RepresentationPair.instNormedAddCommGroupF RepresentationPair.instInnerProductSpaceF
  RepresentationPair.instCompleteSpaceF

namespace RepresentationPair

variable {A B}

/-- The commuting spatial pair `a ↦ π a ⊗ 1`, `b ↦ 1 ⊗ ρ b` on `E ⊗₂ F` of a pair of
representations. -/
abbrev spatial (p : RepresentationPair A B) : CommutingRepresentationPair A B :=
  CommutingRepresentationPair.spatial p.left p.right

variable (A B) in
/-- There is a pair of representations whose spatial commuting pair has injective integrated
form, with norm `‖a‖ ‖b‖` at every `a ⊗ b`: a pair of faithful representations. -/
theorem exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul :
    ∃ p : RepresentationPair A B, Function.Injective p.spatial.tensorHom ∧
      ∀ a b, ‖p.spatial.tensorHom (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  obtain ⟨E, _, _, _, π, hπ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation A
  obtain ⟨F, _, _, _, ρ, hρ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation B
  refine ⟨⟨E, F, π, ρ⟩, CommutingRepresentationPair.tensorHom_spatial_injective hπ hρ,
    fun a b ↦ ?_⟩
  rw [CommutingRepresentationPair.norm_tensorHom_spatial_tmul, NonUnitalStarAlgHom.norm_map π hπ,
    NonUnitalStarAlgHom.norm_map ρ hρ]

instance : Nonempty (RepresentationPair A B) :=
  (exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul A B).nonempty

end RepresentationPair

namespace CommutingRepresentationPair

/-- There is a commuting pair whose integrated form is injective and has norm `‖a‖ ‖b‖` at every
`a ⊗ b`: the spatial pair of faithful representations. -/
theorem exists_tensorHom_injective_and_norm_tensorHom_tmul :
    ∃ p : CommutingRepresentationPair A B, Function.Injective p.tensorHom ∧
      ∀ a b, ‖p.tensorHom (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ :=
  let ⟨p, h⟩ :=
    RepresentationPair.exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul A B
  ⟨p.spatial, h⟩

/-- There is a commuting pair whose integrated form is injective. -/
theorem exists_tensorHom_injective :
    ∃ p : CommutingRepresentationPair A B, Function.Injective p.tensorHom :=
  (exists_tensorHom_injective_and_norm_tensorHom_tmul A B).imp fun _ ↦ And.left

instance : Nonempty (CommutingRepresentationPair A B) :=
  (exists_tensorHom_injective A B).nonempty

end CommutingRepresentationPair

open CommutingRepresentationPair

/-! ### The supremum of the norms of a family of commuting pairs -/

section SupTensorNorm

variable {A B} {ι : Sort*} (f : ι → CommutingRepresentationPair A B)

/-- The supremum `⨆ i, ‖(f i).tensorHom x‖` of the norms on `A ⊗[ℂ] B` coming from a family `f`
of commuting pairs. The maximal norm `TauCeti.maxTensorNorm` is the supremum over all commuting
pairs, and the minimal norm `TauCeti.minTensorNorm` the supremum over the spatial pairs. -/
def supTensorNorm (x : A ⊗[ℂ] B) : ℝ :=
  ⨆ i, ‖(f i).tensorHom x‖

/-- Unfolding `TauCeti.supTensorNorm`. -/
theorem supTensorNorm_def (x : A ⊗[ℂ] B) : supTensorNorm f x = ⨆ i, ‖(f i).tensorHom x‖ :=
  (rfl)

/-- The supremum dominates the norm coming from each member of the family. -/
theorem norm_tensorHom_le_supTensorNorm (i : ι) (x : A ⊗[ℂ] B) :
    ‖(f i).tensorHom x‖ ≤ supTensorNorm f x :=
  let ⟨c, hc⟩ := bddAbove_range_norm_tensorHom x
  le_ciSup (f := fun i ↦ ‖(f i).tensorHom x‖) ⟨c, by rintro _ ⟨j, rfl⟩; exact hc ⟨f j, rfl⟩⟩ i

/-- To bound the supremum by `c ≥ 0` it suffices to bound every member of the family. -/
theorem supTensorNorm_le_of_forall {x : A ⊗[ℂ] B} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ‖(f i).tensorHom x‖ ≤ c) : supTensorNorm f x ≤ c :=
  Real.iSup_le h hc

theorem supTensorNorm_nonneg (x : A ⊗[ℂ] B) : 0 ≤ supTensorNorm f x :=
  Real.iSup_nonneg fun _ ↦ norm_nonneg _

/-- The supremum at `Σ aᵢ ⊗ bᵢ` is at most `Σ ‖aᵢ‖ ‖bᵢ‖`. -/
theorem supTensorNorm_le_sum {κ : Type*} (s : Finset κ) (a : κ → A) (b : κ → B) :
    supTensorNorm f (∑ i ∈ s, a i ⊗ₜ b i) ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ :=
  supTensorNorm_le_of_forall f (by positivity) fun i ↦ (f i).norm_tensorHom_sum_le s a b

theorem supTensorNorm_tmul_le (a : A) (b : B) : supTensorNorm f (a ⊗ₜ b) ≤ ‖a‖ * ‖b‖ := by
  simpa using supTensorNorm_le_sum f {()} (fun _ ↦ a) (fun _ ↦ b)

@[simp]
theorem supTensorNorm_zero : supTensorNorm f 0 = 0 :=
  le_antisymm (supTensorNorm_le_of_forall f le_rfl fun _ ↦ by simp) (supTensorNorm_nonneg f 0)

theorem supTensorNorm_add_le (x y : A ⊗[ℂ] B) :
    supTensorNorm f (x + y) ≤ supTensorNorm f x + supTensorNorm f y :=
  supTensorNorm_le_of_forall f (add_nonneg (supTensorNorm_nonneg f x) (supTensorNorm_nonneg f y))
    fun i ↦ by
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (norm_tensorHom_le_supTensorNorm f i x)
        (norm_tensorHom_le_supTensorNorm f i y))

theorem supTensorNorm_smul (c : ℂ) (x : A ⊗[ℂ] B) :
    supTensorNorm f (c • x) = ‖c‖ * supTensorNorm f x := by
  simp_rw [supTensorNorm_def, map_smul, norm_smul]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

@[simp]
theorem supTensorNorm_neg (x : A ⊗[ℂ] B) : supTensorNorm f (-x) = supTensorNorm f x := by
  simpa using supTensorNorm_smul f (-1) x

@[simp]
theorem supTensorNorm_star (x : A ⊗[ℂ] B) : supTensorNorm f (star x) = supTensorNorm f x := by
  simp_rw [supTensorNorm_def, map_star, norm_star]

theorem supTensorNorm_mul_le (x y : A ⊗[ℂ] B) :
    supTensorNorm f (x * y) ≤ supTensorNorm f x * supTensorNorm f y :=
  supTensorNorm_le_of_forall f (mul_nonneg (supTensorNorm_nonneg f x) (supTensorNorm_nonneg f y))
    fun i ↦ by
      rw [map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul (norm_tensorHom_le_supTensorNorm f i x)
        (norm_tensorHom_le_supTensorNorm f i y) (norm_nonneg _) (supTensorNorm_nonneg f x))

/-- **The C*-identity** for the supremum of the norms of a family of commuting pairs. -/
theorem supTensorNorm_star_mul_self (x : A ⊗[ℂ] B) :
    supTensorNorm f (star x * x) = supTensorNorm f x ^ 2 := by
  have hp (i : ι) : ‖(f i).tensorHom (star x * x)‖ = ‖(f i).tensorHom x‖ ^ 2 := by
    rw [map_mul, map_star, CStarRing.norm_star_mul_self, sq]
  refine le_antisymm (supTensorNorm_le_of_forall f (sq_nonneg _) fun i ↦ ?_) ?_
  · rw [hp]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_tensorHom_le_supTensorNorm f i x) 2
  · have h : supTensorNorm f x ≤ √(supTensorNorm f (star x * x)) :=
      supTensorNorm_le_of_forall f (Real.sqrt_nonneg _) fun i ↦ by
        rw [← Real.sqrt_sq (norm_nonneg ((f i).tensorHom x)), ← hp]
        exact Real.sqrt_le_sqrt (norm_tensorHom_le_supTensorNorm f i _)
    calc supTensorNorm f x ^ 2 ≤ √(supTensorNorm f (star x * x)) ^ 2 :=
          pow_le_pow_left₀ (supTensorNorm_nonneg f x) h 2
      _ = supTensorNorm f (star x * x) := Real.sq_sqrt (supTensorNorm_nonneg f _)

/-- If the family contains a commuting pair with injective integrated form, the supremum is
definite: it vanishes only at `0`. -/
theorem supTensorNorm_eq_zero_iff (hf : ∃ i, Function.Injective (f i).tensorHom)
    {x : A ⊗[ℂ] B} : supTensorNorm f x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ supTensorNorm_zero f⟩
  obtain ⟨i, hi⟩ := hf
  refine hi ?_
  rw [map_zero, ← norm_eq_zero]
  exact le_antisymm (hx ▸ norm_tensorHom_le_supTensorNorm f i x) (norm_nonneg _)

/-- If some member of the family has norm `‖a‖ ‖b‖` at `a ⊗ b`, so does the supremum. -/
theorem supTensorNorm_tmul {a : A} {b : B} (h : ∃ i, ‖(f i).tensorHom (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖) :
    supTensorNorm f (a ⊗ₜ b) = ‖a‖ * ‖b‖ := by
  obtain ⟨i, hi⟩ := h
  exact le_antisymm (supTensorNorm_tmul_le f a b) (hi ▸ norm_tensorHom_le_supTensorNorm f i _)

end SupTensorNorm

/-! ### The maximal norm -/

/-- The **maximal C*-norm** `‖x‖_max` on `A ⊗[ℂ] B`: the supremum of `‖(π × ρ) x‖` over all
commuting pairs of representations `π` of `A` and `ρ` of `B` on Hilbert spaces in the universe
`max u v`. -/
def maxTensorNorm (x : A ⊗[ℂ] B) : ℝ :=
  supTensorNorm id x

/-- Unfolding `TauCeti.maxTensorNorm`. -/
theorem maxTensorNorm_def (x : A ⊗[ℂ] B) :
    maxTensorNorm A B x = ⨆ p : CommutingRepresentationPair A B, ‖p.tensorHom x‖ :=
  (rfl)

variable {A B}

/-- The maximal norm dominates the norm coming from every commuting pair. -/
theorem norm_tensorHom_le_maxTensorNorm (p : CommutingRepresentationPair A B) (x : A ⊗[ℂ] B) :
    ‖p.tensorHom x‖ ≤ maxTensorNorm A B x :=
  norm_tensorHom_le_supTensorNorm id p x

/-- To bound the maximal norm it suffices to bound every commuting pair. -/
theorem maxTensorNorm_le_of_forall {x : A ⊗[ℂ] B} {c : ℝ}
    (h : ∀ p : CommutingRepresentationPair A B, ‖p.tensorHom x‖ ≤ c) : maxTensorNorm A B x ≤ c := by
  rw [maxTensorNorm_def]
  exact ciSup_le h

theorem maxTensorNorm_nonneg (x : A ⊗[ℂ] B) : 0 ≤ maxTensorNorm A B x :=
  supTensorNorm_nonneg id x

/-- The supremum over any family of commuting pairs is at most the maximal norm. -/
theorem supTensorNorm_le_maxTensorNorm {ι : Sort*} (f : ι → CommutingRepresentationPair A B)
    (x : A ⊗[ℂ] B) : supTensorNorm f x ≤ maxTensorNorm A B x :=
  supTensorNorm_le_of_forall f (maxTensorNorm_nonneg x) fun i ↦
    norm_tensorHom_le_maxTensorNorm (f i) x

/-- The maximal norm of `Σ aᵢ ⊗ bᵢ` is at most `Σ ‖aᵢ‖ ‖bᵢ‖`. -/
theorem maxTensorNorm_le_sum {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B) :
    maxTensorNorm A B (∑ i ∈ s, a i ⊗ₜ b i) ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ :=
  supTensorNorm_le_sum id s a b

theorem maxTensorNorm_tmul_le (a : A) (b : B) : maxTensorNorm A B (a ⊗ₜ b) ≤ ‖a‖ * ‖b‖ :=
  supTensorNorm_tmul_le id a b

@[simp]
theorem maxTensorNorm_zero : maxTensorNorm A B 0 = 0 :=
  supTensorNorm_zero id

theorem maxTensorNorm_add_le (x y : A ⊗[ℂ] B) :
    maxTensorNorm A B (x + y) ≤ maxTensorNorm A B x + maxTensorNorm A B y :=
  supTensorNorm_add_le id x y

theorem maxTensorNorm_smul (c : ℂ) (x : A ⊗[ℂ] B) :
    maxTensorNorm A B (c • x) = ‖c‖ * maxTensorNorm A B x :=
  supTensorNorm_smul id c x

@[simp]
theorem maxTensorNorm_neg (x : A ⊗[ℂ] B) : maxTensorNorm A B (-x) = maxTensorNorm A B x :=
  supTensorNorm_neg id x

@[simp]
theorem maxTensorNorm_star (x : A ⊗[ℂ] B) : maxTensorNorm A B (star x) = maxTensorNorm A B x :=
  supTensorNorm_star id x

theorem maxTensorNorm_mul_le (x y : A ⊗[ℂ] B) :
    maxTensorNorm A B (x * y) ≤ maxTensorNorm A B x * maxTensorNorm A B y :=
  supTensorNorm_mul_le id x y

/-- **The C*-identity** for the maximal norm. -/
theorem maxTensorNorm_star_mul_self (x : A ⊗[ℂ] B) :
    maxTensorNorm A B (star x * x) = maxTensorNorm A B x ^ 2 :=
  supTensorNorm_star_mul_self id x

/-- The maximal norm is definite: it vanishes only at `0`. -/
@[simp]
theorem maxTensorNorm_eq_zero_iff {x : A ⊗[ℂ] B} : maxTensorNorm A B x = 0 ↔ x = 0 :=
  supTensorNorm_eq_zero_iff id (exists_tensorHom_injective A B)

/-- The maximal norm is a **cross norm**: `‖a ⊗ b‖_max = ‖a‖ ‖b‖`. -/
@[simp]
theorem maxTensorNorm_tmul (a : A) (b : B) : maxTensorNorm A B (a ⊗ₜ b) = ‖a‖ * ‖b‖ :=
  supTensorNorm_tmul id <|
    (exists_tensorHom_injective_and_norm_tensorHom_tmul A B).imp fun _ h ↦ h.2 a b

/-- **Universal bound.** Commuting star homomorphisms `φ : A → C` and `ψ : B → C` into a
C*-algebra `C` in the universe `max u v` integrate to a star homomorphism `A ⊗[ℂ] B → C` bounded
by the maximal norm. -/
theorem norm_liftNonUnitalStarAlgHom_le_maxTensorNorm {C : Type (max u v)} [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] C) (h : ∀ a b, Commute (φ a) (ψ b)) (x : A ⊗[ℂ] B) :
    ‖Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h x‖ ≤ maxTensorNorm A B x := by
  obtain ⟨K, _, _, _, σ, hσ, -⟩ := CStarAlgebra.exists_faithful_nondegenerate_representation C
  let p : CommutingRepresentationPair A B :=
    { H := K
      left := σ.comp φ
      right := σ.comp ψ
      commute a b := (h a b).map σ }
  have hpx : p.tensorHom x = σ (Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a b =>
      rw [tensorHom_tmul, Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul, map_mul]
      simp [p]
  rw [← NonUnitalStarAlgHom.norm_map σ hσ, ← hpx]
  exact norm_tensorHom_le_maxTensorNorm p x

end TauCeti
