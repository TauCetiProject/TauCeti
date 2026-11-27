/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.BaseChange
public import TauCeti.RingTheory.Grassmannian.Incidence
public import TauCeti.RingTheory.Grassmannian.StableLocus
public import TauCeti.LinearAlgebra.Quotient.Exact
public import TauCeti.LinearAlgebra.TensorProduct.Range

import TauCeti.Algebra.Module.Projective.Complement
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Images of quotient Grassmannian points under injections

An injection `i : M → N` with finite projective cokernel of constant rank `d` sends a
rank-`r` quotient kernel `S` to `i(S)`, a quotient kernel of rank `r + d`. Its image consists
exactly of the kernels contained in `i(M)`. The construction is natural over arbitrary
coefficient algebras and respects intertwined endomorphisms. The cokernel is specified by a
point `P` of the quotient Grassmannian whose submodule is the range of `i`.

The quotient sequence `0 → M/S → N/i(S) → N/i(M) → 0` splits by projectivity of its last
term. No invariant complement, flat coefficient algebra, or reducedness assumption is used.
The equivalence `mapEquivOfInjectiveBaseChange` identifies the image over every coefficient
algebra with the kernels contained in `P`. The scheme-theoretic incidence description is
proved in `TauCeti.AlgebraicGeometry.Grassmannian.Map`.

## References

* The Stacks Project, Tag 089R, for the quotient Grassmannian functor.
-/

public section

universe u v v' w

open TensorProduct

namespace LinearMap

open scoped Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module R N] {d : ℕ}
  {A : Type w} [CommRing A] [Algebra R A]

/-- A quotient presentation of the cokernel makes an injection universally injective. -/
theorem baseChange_injective_of_toSubmodule_eq_range (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) :
    Function.Injective (i.baseChange A) :=
  i.baseChange_injective_of_isComplemented hi (by
    rw [← hP]; exact P.toSubmodule.isComplemented_of_projective_quotient)

end LinearMap

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module R N] {r d : ℕ}

private theorem rankAtStalk_quotient_range (i : M →ₗ[R] N) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) (N ⧸ LinearMap.range i) p = d :=
  (congrFun (Module.rankAtStalk_eq_of_equiv
    (Submodule.quotEquivOfEq _ _ hP).symm) p).trans (P.rankAtStalk_eq p)

/-- An injection with finite projective rank-`d` cokernel sends a quotient kernel of rank `r`
to its image, of quotient rank `r + d`. -/
noncomputable def mapOfInjective (S : G(r, M; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    G(r + d, N; R) := by
  haveI : Module.Projective R (N ⧸ LinearMap.range i) := by rw [← hP]; infer_instance
  haveI : Module.Finite R (N ⧸ LinearMap.range i) := by rw [← hP]; infer_instance
  let e := (S.toSubmodule.nonempty_quotient_map_equiv_prod i hi).some
  exact
    { toSubmodule := S.toSubmodule.map i
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq p := by
        rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
        simp only [Pi.add_apply, S.rankAtStalk_eq]
        exact congrArg (r + ·) (rankAtStalk_quotient_range i P hP p) }

/-- The kernel of the image point is the image of the kernel. -/
@[simp]
theorem toSubmodule_mapOfInjective (S : G(r, M; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    (S.mapOfInjective i hi P hP).toSubmodule = S.toSubmodule.map i := (rfl)

/-- A quotient kernel contained in the range of an injection descends to the source, with
quotient rank decreased by the constant cokernel rank. -/
noncomputable def comapOfInjective (T : G(r + d, N; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (hT : T.toSubmodule ≤ P.toSubmodule) : G(r, M; R) := by
  haveI : Module.Projective R (N ⧸ LinearMap.range i) := by rw [← hP]; infer_instance
  haveI : Module.Finite R (N ⧸ LinearMap.range i) := by rw [← hP]; infer_instance
  let S := T.toSubmodule.comap i
  have hS : S.map i = T.toSubmodule := Submodule.map_comap_eq_self (hT.trans hP.le)
  let e : (N ⧸ T.toSubmodule) ≃ₗ[R] (M ⧸ S) × (N ⧸ LinearMap.range i) :=
    (Submodule.quotEquivOfEq _ _ hS.symm).trans
      (S.nonempty_quotient_map_equiv_prod i hi).some
  let π := LinearMap.fst R (M ⧸ S) (N ⧸ LinearMap.range i) ∘ₗ e.toLinearMap
  let ι := e.symm.toLinearMap ∘ₗ LinearMap.inl R (M ⧸ S) (N ⧸ LinearMap.range i)
  haveI : Module.Finite R (M ⧸ S) :=
    Module.Finite.of_surjective π (Prod.fst_surjective.comp e.surjective)
  haveI : Module.Projective R (M ⧸ S) :=
    Module.Projective.of_split ι π (by ext x; simp [π, ι])
  exact
    { toSubmodule := S
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq p := by
        have h := T.rankAtStalk_eq p
        rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod] at h
        simp only [Pi.add_apply] at h
        rw [rankAtStalk_quotient_range i P hP p] at h
        omega }

/-- Descent along an injection takes inverse images of kernels. -/
@[simp]
theorem toSubmodule_comapOfInjective (T : G(r + d, N; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (hT : T.toSubmodule ≤ P.toSubmodule) :
    (T.comapOfInjective i hi P hP hT).toSubmodule = T.toSubmodule.comap i := (rfl)

/-- Images identify the source Grassmannian with the quotient kernels in the target contained
in the range of the injection. -/
noncomputable def mapEquivOfInjective (r : ℕ) (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    G(r, M; R) ≃ {T : G(r + d, N; R) // T.toSubmodule ≤ P.toSubmodule} where
  toFun S := ⟨S.mapOfInjective i hi P hP, by
    rw [toSubmodule_mapOfInjective, hP]; exact LinearMap.map_le_range⟩
  invFun T := T.val.comapOfInjective i hi P hP T.property
  left_inv S := Grassmannian.ext <| by
    simp [Submodule.comap_map_eq, LinearMap.ker_eq_bot.mpr hi]
  right_inv T := Subtype.ext <| Grassmannian.ext <| by
    simp only [toSubmodule_mapOfInjective, toSubmodule_comapOfInjective]
    exact Submodule.map_comap_eq_self (T.property.trans hP.le)

/-- Successive image kernels agree with the composite injection, after associating the
sum of quotient ranks. The point `Q` presents the cokernel of the composite. -/
theorem mapOfInjective_comp {L : Type*} [AddCommGroup L] [Module R L] {d' : ℕ}
    (S : G(r, M; R)) (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (j : N →ₗ[R] L) (hj : Function.Injective j)
    (P' : G(d', L; R)) (hP' : P'.toSubmodule = LinearMap.range j)
    (Q : G(d + d', L; R)) (hQ : Q.toSubmodule = LinearMap.range (j ∘ₗ i)) :
    cast (congrArg (fun n ↦ G(n, L; R)) (Nat.add_assoc r d d'))
      ((S.mapOfInjective i hi P hP).mapOfInjective j hj P' hP') =
      S.mapOfInjective (j ∘ₗ i) (hj.comp hi) Q hQ := by
  have hcast {a b : ℕ} (h : a = b) (T : G(a, L; R)) :
      (cast (congrArg (fun n ↦ G(n, L; R)) h) T).toSubmodule = T.toSubmodule := by
    cases h
    rfl
  apply Grassmannian.ext
  rw [hcast (Nat.add_assoc r d d'), toSubmodule_mapOfInjective, toSubmodule_mapOfInjective,
    toSubmodule_mapOfInjective, Submodule.map_comp]

/-- The forward image equivalence takes the image kernel. -/
@[simp]
theorem mapEquivOfInjective_apply_val (S : G(r, M; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    (mapEquivOfInjective r i hi P hP S).val = S.mapOfInjective i hi P hP := (rfl)

/-- The inverse image equivalence takes the inverse image of the kernel. -/
@[simp]
theorem toSubmodule_mapEquivOfInjective_symm_apply (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (T : {T : G(r + d, N; R) // T.toSubmodule ≤ P.toSubmodule}) :
    ((mapEquivOfInjective r i hi P hP).symm T).toSubmodule = T.val.toSubmodule.comap i := (rfl)

/-- The map induced by an injection is injective. -/
theorem mapOfInjective_injective (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    Function.Injective (fun S : G(r, M; R) ↦ S.mapOfInjective i hi P hP) := by
  intro S S' h
  exact (mapEquivOfInjective r i hi P hP).injective (Subtype.ext h)

/-- The image of the injection construction is precisely the upper incidence condition. -/
theorem exists_mapOfInjective_eq_iff (T : G(r + d, N; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    (∃ S : G(r, M; R), S.mapOfInjective i hi P hP = T) ↔
      T.toSubmodule ≤ P.toSubmodule := by
  constructor
  · rintro ⟨S, rfl⟩
    exact (mapEquivOfInjective r i hi P hP S).property
  · intro h
    exact ⟨(mapEquivOfInjective r i hi P hP).symm ⟨T, h⟩,
      congrArg Subtype.val ((mapEquivOfInjective r i hi P hP).apply_symm_apply ⟨T, h⟩)⟩

/-- An intertwined injection reflects as well as preserves stability of an image kernel. -/
theorem mapOfInjective_mem_invtSubmodule_iff (S : G(r, M; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (t : Module.End R M) (u : Module.End R N) (htu : i ∘ₗ t = u ∘ₗ i) :
    (S.mapOfInjective i hi P hP).toSubmodule ∈ u.invtSubmodule ↔
      S.toSubmodule ∈ t.invtSubmodule := by
  rw [toSubmodule_mapOfInjective, Module.End.mem_invtSubmodule,
    Module.End.mem_invtSubmodule]
  constructor
  · intro h x hx
    have hx' : i (t x) ∈ S.toSubmodule.map i := by
      simpa only [LinearMap.comp_apply] using
        (LinearMap.congr_fun htu x).symm ▸ h ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, he⟩
    rw [Submodule.mem_comap, ← hi he]
    exact hy
  · rintro h _ ⟨x, hx, rfl⟩
    exact ⟨t x, h hx, LinearMap.congr_fun htu x⟩

section Coefficients

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The extended cokernel presentation has kernel the range of the extended injection. -/
theorem toSubmodule_baseChange_eq_range (P : G(d, N; R)) (i : M →ₗ[R] N)
    (hP : P.toSubmodule = LinearMap.range i) :
    (P.baseChange A).toSubmodule = LinearMap.range (i.baseChange A) := by
  rw [toSubmodule_baseChange, hP, LinearMap.baseChange_range]

/-- Over every coefficient algebra, image kernels identify the source Grassmannian with the
upper incidence subfunctor. -/
noncomputable def mapEquivOfInjectiveBaseChange (r : ℕ) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (A : Type w) [CommRing A] [Algebra R A] :
    G(r, A ⊗[R] M; A) ≃
      {T : G(r + d, A ⊗[R] N; A) // T.toSubmodule ≤ (P.baseChange A).toSubmodule} :=
  mapEquivOfInjective r (i.baseChange A)
    (i.baseChange_injective_of_toSubmodule_eq_range hi P hP)
    (P.baseChange A) (P.toSubmodule_baseChange_eq_range i hP)

/-- The injection construction on points over a coefficient algebra. -/
noncomputable def mapOfInjectiveBaseChange (S : G(r, A ⊗[R] M; A)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    G(r + d, A ⊗[R] N; A) :=
  (mapEquivOfInjectiveBaseChange r i hi P hP A S).val

/-- On every coefficient algebra the injection construction takes images of kernels. -/
@[simp]
theorem toSubmodule_mapOfInjectiveBaseChange (S : G(r, A ⊗[R] M; A)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    (S.mapOfInjectiveBaseChange i hi P hP).toSubmodule =
      S.toSubmodule.map (i.baseChange A) := (rfl)

/-- Extending scalars in an image kernel is the injection construction after extending scalars.
No flatness assumption on the coefficient algebra is required. -/
@[simp]
theorem baseChange_mapOfInjective (S : G(r, M; R)) (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i) :
    (S.mapOfInjective i hi P hP).baseChange A =
      (S.baseChange A).mapOfInjectiveBaseChange i hi P hP := by
  ext : 1
  simp only [toSubmodule_baseChange, toSubmodule_mapOfInjective,
    toSubmodule_mapOfInjectiveBaseChange, Submodule.baseChange_map]

/-- The value of the coefficientwise image equivalence is the image-kernel construction. -/
@[simp]
theorem mapEquivOfInjectiveBaseChange_apply_val (S : G(r, A ⊗[R] M; A))
    (i : M →ₗ[R] N) (hi : Function.Injective i) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) :
    (mapEquivOfInjectiveBaseChange r i hi P hP A S).val =
      S.mapOfInjectiveBaseChange i hi P hP := (rfl)

/-- The inverse coefficientwise image equivalence takes the inverse image of the kernel. -/
@[simp]
theorem toSubmodule_mapEquivOfInjectiveBaseChange_symm_apply (i : M →ₗ[R] N)
    (hi : Function.Injective i) (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (T : {T : G(r + d, A ⊗[R] N; A) // T.toSubmodule ≤ (P.baseChange A).toSubmodule}) :
    ((mapEquivOfInjectiveBaseChange r i hi P hP A).symm T).toSubmodule =
      T.val.toSubmodule.comap (i.baseChange A) := (rfl)

/-- Over every coefficient algebra, successive image kernels agree with the composite
injection after associating the quotient ranks. -/
theorem mapOfInjectiveBaseChange_comp {L : Type*} [AddCommGroup L] [Module R L] {d' : ℕ}
    (S : G(r, A ⊗[R] M; A)) (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (j : N →ₗ[R] L) (hj : Function.Injective j)
    (P' : G(d', L; R)) (hP' : P'.toSubmodule = LinearMap.range j)
    (Q : G(d + d', L; R)) (hQ : Q.toSubmodule = LinearMap.range (j ∘ₗ i)) :
    cast (congrArg (fun n ↦ G(n, A ⊗[R] L; A)) (Nat.add_assoc r d d'))
      ((S.mapOfInjectiveBaseChange i hi P hP).mapOfInjectiveBaseChange j hj P' hP') =
      S.mapOfInjectiveBaseChange (j ∘ₗ i) (hj.comp hi) Q hQ := by
  simpa only [mapOfInjectiveBaseChange, mapEquivOfInjectiveBaseChange,
    mapEquivOfInjective_apply_val, LinearMap.baseChange_comp] using
    mapOfInjective_comp S (i.baseChange A) (i.baseChange_injective_of_toSubmodule_eq_range hi P hP)
      (P.baseChange A) (P.toSubmodule_baseChange_eq_range i hP)
      (j.baseChange A) (j.baseChange_injective_of_toSubmodule_eq_range hj P' hP')
      (P'.baseChange A) (P'.toSubmodule_baseChange_eq_range j hP')
      (Q.baseChange A) (by
        simpa only [LinearMap.baseChange_comp] using Q.toSubmodule_baseChange_eq_range (j ∘ₗ i) hQ)

/-- Taking image kernels commutes with arbitrary coefficient maps. -/
@[simp]
theorem map_mapOfInjectiveBaseChange (f : A →ₐ[R] B) (S : G(r, A ⊗[R] M; A))
    (i : M →ₗ[R] N) (hi : Function.Injective i) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) :
    map f (S.mapOfInjectiveBaseChange i hi P hP) =
      (map f S).mapOfInjectiveBaseChange i hi P hP := by
  ext : 1
  simp only [map_toSubmodule_eq_span, toSubmodule_mapOfInjectiveBaseChange,
    Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
  exact congrArg _ (Set.image_congr' rfl fun x ↦
    LinearMap.rTensor_baseChange f x i)

/-- Stability of an image kernel over every test algebra is exactly stability in the source. -/
theorem mapOfInjectiveBaseChange_mem_invtSubmodule_iff (S : G(r, A ⊗[R] M; A))
    (i : M →ₗ[R] N) (hi : Function.Injective i) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (S.mapOfInjectiveBaseChange i hi P hP).toSubmodule ∈ Module.End.invtSubmodule (u.baseChange A) ↔
      S.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A) := by
  apply mapOfInjective_mem_invtSubmodule_iff (i := i.baseChange A)
    (hi := i.baseChange_injective_of_toSubmodule_eq_range hi P hP) (P := P.baseChange A)
    (hP := P.toSubmodule_baseChange_eq_range i hP) (t := t.baseChange A) (u := u.baseChange A)
  simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange A) htu

/-- The stability ideal is unchanged by an intertwined injection. This equality retains the
scheme structure on nonreduced coefficient algebras. -/
theorem stableLocus_mapOfInjectiveBaseChange (S : G(r, A ⊗[R] M; A))
    (i : M →ₗ[R] N) (hi : Function.Injective i) (P : G(d, N; R))
    (hP : P.toSubmodule = LinearMap.range i) (t : Module.End R M) (u : Module.End R N)
    (htu : i ∘ₗ t = u ∘ₗ i) :
    (S.mapOfInjectiveBaseChange i hi P hP).stableLocus u = S.stableLocus t := by
  have hv {B : Type w} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
      Ideal.map f ((S.mapOfInjectiveBaseChange i hi P hP).stableLocus u) = ⊥ ↔
        Ideal.map f (S.stableLocus t) = ⊥ := by
    rw [← stableLocus_map, ← stableLocus_map, map_mapOfInjectiveBaseChange,
      stableLocus_eq_bot_iff, stableLocus_eq_bot_iff,
      mapOfInjectiveBaseChange_mem_invtSubmodule_iff _ i hi P hP t u htu]
  apply le_antisymm
  · have h := (hv (Ideal.Quotient.mkₐ R (S.stableLocus t))).mpr
      (by exact Ideal.map_quotient_self _)
    simpa only [Ideal.map_eq_bot_iff_le_ker, AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker] using h
  · have h := (hv (Ideal.Quotient.mkₐ R
      ((S.mapOfInjectiveBaseChange i hi P hP).stableLocus u))).mp
      (by exact Ideal.map_quotient_self _)
    simpa only [Ideal.map_eq_bot_iff_le_ker, AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker] using h

/-- Changing the ground ring in the injection construction agrees with the canonical tensor
associativity identification. The point `P'` may be any presentation of the extended cokernel. -/
theorem baseChangeEquiv_mapOfInjectiveBaseChange {R' : Type*} [CommRing R'] [Algebra R R']
    [Algebra R' A] [IsScalarTower R R' A]
    (S : G(r, A ⊗[R'] (R' ⊗[R] M); A)) (i : M →ₗ[R] N) (hi : Function.Injective i)
    (P : G(d, N; R)) (hP : P.toSubmodule = LinearMap.range i)
    (hi' : Function.Injective (i.baseChange R')) (P' : G(d, R' ⊗[R] N; R'))
    (hP' : P'.toSubmodule = LinearMap.range (i.baseChange R')) :
    baseChangeEquiv R' (S.mapOfInjectiveBaseChange (i.baseChange R') hi' P' hP') =
      (baseChangeEquiv R' S).mapOfInjectiveBaseChange i hi P hP := by
  ext : 1
  simp only [toSubmodule_baseChangeEquiv, toSubmodule_mapOfInjectiveBaseChange,
    ← Submodule.map_comp]
  congr 1
  ext a
  simp

end Coefficients

end Module.Grassmannian
