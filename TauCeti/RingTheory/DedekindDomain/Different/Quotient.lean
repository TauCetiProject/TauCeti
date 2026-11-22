/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Trace-dual quotient comparison for linear maps

For an integral domain `A` with fraction field `K`, a finite separable extension `L / K`, and the
integral closure `B` of `A` in `L` with `Bᵛ = Submodule.traceDual A K (1 : Submodule B L)`, the
trace descends to `traceDualQuotientMap : L ⧸ Bᵛ →ₗ[A] K ⧸ A`, yielding `traceDualLinearMapEquiv :
(M →ₗ[B] (L ⧸ Bᵛ)) ≃ₗ[A] (M →ₗ[A] (K ⧸ A))` when `B` is finite projective over `A`.

When `A` is integrally closed, `directTracePairing : L ⧸ B →ₗ[A] (B →ₗ[A] K ⧸ A)` has kernel the
image of `Bᵛ` in `L ⧸ B`. When moreover `B` is a Dedekind domain (with `A` integrally closed and
`B` torsion-free over `A`), if `differentIdeal A B` is principal then dividing by a generator
identifies `L ⧸ B ≃ₗ[B] L ⧸ Bᵛ`, and `directTracePairing` is injective iff `differentIdeal A B = ⊤`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section
noncomputable section

namespace TauCeti

section TraceDualQuotient

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

/-- The `A`-linear map `L ⧸ Bᵛ → K ⧸ A` induced by `Algebra.trace K L`. -/
def traceDualQuotientMap :
    (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) →ₗ[A] (K ⧸ (1 : Submodule A K)) :=
  ((Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A).liftQ
    ((1 : Submodule A K).mkQ ∘ₗ (Algebra.trace K L).restrictScalars A) fun x hx ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      simpa [Algebra.traceForm_apply] using
        Submodule.mem_traceDual.mp hx 1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
@[simp] theorem traceDualQuotientMap_mk (x : L) :
    traceDualQuotientMap A K B L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Algebra.trace K L x) := (rfl)

/-- For `y ∈ Bᵛ`, multiplication by `y` descends to an `A`-linear map `K ⧸ A → L ⧸ Bᵛ`. -/
def mulByTraceDualQuotientMap (y : L) (hy : y ∈ Submodule.traceDual A K (1 : Submodule B L)) :
    (K ⧸ (1 : Submodule A K)) →ₗ[A] (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) :=
  (1 : Submodule A K).liftQ
    { toFun := fun k ↦ Submodule.Quotient.mk (k • y)
      map_add' := fun _ _ ↦ by rw [add_smul, Submodule.Quotient.mk_add]
      map_smul' := fun _ _ ↦ by simp only [RingHom.id_apply, smul_assoc]; rfl } fun k hk ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hk
      rw [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_eq_zero,
        algebraMap_smul, ← algebraMap_smul B a y]
      exact (Submodule.traceDual A K (1 : Submodule B L)).smul_mem (algebraMap A B a) hy
@[simp] theorem mulByTraceDualQuotientMap_mk (y : L)
    (hy : y ∈ Submodule.traceDual A K (1 : Submodule B L)) (k : K) :
    mulByTraceDualQuotientMap A K B L y hy (Submodule.Quotient.mk k) =
      Submodule.Quotient.mk (k • y) := (rfl)

end TraceDualQuotient

section TraceDualEquiv

/-- `Hom_A(B, N)` equipped with the precomposition `B`-module structure `(b • f) b' = f (b' * b)`.
Kept private to keep `traceDualLinearMapEquiv` universe-polymorphic across `A`, `K`, `B`, `L`, `M`
without requiring `ModuleCat`. -/
private structure PrecompLinearMap (A B N : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] where
  toLinearMap : B →ₗ[A] N

private def PrecompLinearMap.equiv (A B N : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] :
    PrecompLinearMap A B N ≃ (B →ₗ[A] N) where
  toFun := PrecompLinearMap.toLinearMap
  invFun := PrecompLinearMap.mk

private instance {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] : AddCommGroup (PrecompLinearMap A B N) :=
  (PrecompLinearMap.equiv A B N).addCommGroup

@[simp] private theorem PrecompLinearMap.add_apply {A B N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] (f g : PrecompLinearMap A B N) (b : B) :
    (f + g).toLinearMap b = f.toLinearMap b + g.toLinearMap b :=
  LinearMap.add_apply f.toLinearMap g.toLinearMap b

private instance {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] : Module B (PrecompLinearMap A B N) where
  smul b f := ⟨{
    toFun := fun b' ↦ f.toLinearMap (b' * b)
    map_add' := fun _ _ ↦ by simp [add_mul]
    map_smul' := fun _ _ ↦ by simp }⟩
  one_smul f := (PrecompLinearMap.equiv A B N).injective <| by
    ext b'; change f.toLinearMap (b' * 1) = f.toLinearMap b'; rw [mul_one]
  mul_smul b₁ b₂ f := (PrecompLinearMap.equiv A B N).injective <| by
    ext b'; change f.toLinearMap (b' * (b₁ * b₂)) = f.toLinearMap (b' * b₁ * b₂); rw [mul_assoc]
  smul_zero b := (PrecompLinearMap.equiv A B N).injective <| by ext b'; rfl
  smul_add b f g := (PrecompLinearMap.equiv A B N).injective <| by
    ext b'; change (f + g).toLinearMap (b' * b) = f.toLinearMap (b' * b) + g.toLinearMap (b' * b)
    exact PrecompLinearMap.add_apply f g (b' * b)
  add_smul b₁ b₂ f := (PrecompLinearMap.equiv A B N).injective <| by
    ext b'
    change f.toLinearMap (b' * (b₁ + b₂)) = f.toLinearMap (b' * b₁) + f.toLinearMap (b' * b₂)
    rw [mul_add, map_add]
  zero_smul f := (PrecompLinearMap.equiv A B N).injective <| by
    ext b'; change f.toLinearMap (b' * 0) = 0; rw [mul_zero, map_zero]

private instance {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] : Module A (PrecompLinearMap A B N) :=
  Module.compHom (PrecompLinearMap A B N) (algebraMap A B)

private instance {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] : IsScalarTower A B (PrecompLinearMap A B N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private theorem PrecompLinearMap.smul_apply {A B N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] (b b' : B) (f : PrecompLinearMap A B N) :
    (b • f).toLinearMap b' = f.toLinearMap (b' * b) := rfl

private theorem PrecompLinearMap.smul_apply_ring {A B N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] (a : A) (f : PrecompLinearMap A B N) (b : B) :
    (a • f).toLinearMap b = a • f.toLinearMap b := by
  change (algebraMap A B a • f).toLinearMap b = a • f.toLinearMap b
  rw [PrecompLinearMap.smul_apply, mul_comm, ← Algebra.smul_def, map_smul]

/-- Adjunction-like `A`-linear equivalence `(M →ₗ[B] Hom_A(B, N)) ≃ₗ[A] (M →ₗ[A] N)` for
universe-polymorphic `A`, `B`, `N`, `M`. -/
private def coextendHomEquiv (A B N M : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] :
    (M →ₗ[B] PrecompLinearMap A B N) ≃ₗ[A] (M →ₗ[A] N) where
  toFun φ :=
    { toFun := fun m ↦ (φ m).toLinearMap 1
      map_add' := fun m₁ m₂ ↦ by rw [map_add, PrecompLinearMap.add_apply]
      map_smul' := fun a m ↦ by
        have hsm : a • φ m = algebraMap A B a • φ m := rfl
        rw [RingHom.id_apply, ← algebraMap_smul B a m, map_smul, ← hsm,
          PrecompLinearMap.smul_apply_ring] }
  invFun ψ :=
    { toFun := fun m ↦ ⟨{
        toFun := fun b ↦ ψ (b • m)
        map_add' := fun b₁ b₂ ↦ by rw [add_smul, map_add]
        map_smul' := fun a b ↦ by rw [RingHom.id_apply, smul_assoc, map_smul] }⟩
      map_add' := fun m₁ m₂ ↦ (PrecompLinearMap.equiv A B N).injective <| by
        ext b
        change ψ (b • (m₁ + m₂)) =
          ((⟨_⟩ : PrecompLinearMap A B N) + (⟨_⟩ : PrecompLinearMap A B N)).toLinearMap b
        rw [PrecompLinearMap.add_apply, smul_add, map_add]; rfl
      map_smul' := fun b m ↦ (PrecompLinearMap.equiv A B N).injective <| by
        ext b'
        change ψ (b' • (b • m)) = (b • (⟨_⟩ : PrecompLinearMap A B N)).toLinearMap b'
        rw [PrecompLinearMap.smul_apply, ← mul_smul]; rfl }
  left_inv φ := LinearMap.ext fun m ↦ (PrecompLinearMap.equiv A B N).injective <| by
    ext b
    change (φ (b • m)).toLinearMap 1 = (φ m).toLinearMap b
    rw [map_smul, PrecompLinearMap.smul_apply, one_mul]
  right_inv ψ := LinearMap.ext fun m ↦ by simp [one_smul]
  map_add' _ _ := LinearMap.ext fun m ↦ PrecompLinearMap.add_apply _ _ 1
  map_smul' _ _ := LinearMap.ext fun m ↦ PrecompLinearMap.smul_apply_ring _ _ 1

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L]

omit [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L] in
/-- Isolate scalar-tower transport `a • b = (a : K) • (b : L)` in the extension tower. -/
private theorem algebraMap_smul_eq_smul_algebraMap (a : A) (b : B) :
    algebraMap B L (a • b) = algebraMap A K a • algebraMap B L b := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B L,
    IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def]

omit [IsDomain A] [IsFractionRing A K] in
/-- Reconstruct `w : B` as `∑ i, a i • b i` from its traces against a dual family `(b, y)`. -/
private theorem sum_smul_eq_of_dualFamily {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (w : B) (a : Fin n → A)
    (ha : ∀ i, algebraMap A K (a i) = Algebra.trace K L (y i * algebraMap B L w)) :
    ∑ i, a i • b i = w := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate K L).1 _ fun x ↦ ?_
  have hterm (i : Fin n) :
      Algebra.trace K L (x * algebraMap B L (a i • b i)) =
        Algebra.trace K L (x * algebraMap B L (b i)) *
          Algebra.trace K L (y i * algebraMap B L w) := by
    calc Algebra.trace K L (x * algebraMap B L (a i • b i))
      = Algebra.trace K L (algebraMap A K (a i) • (x * algebraMap B L (b i))) := by
          rw [algebraMap_smul_eq_smul_algebraMap A K B L, mul_smul_comm]
    _ = Algebra.trace K L (x * algebraMap B L (b i)) * algebraMap A K (a i) := by
          rw [map_smul, smul_eq_mul, mul_comm]
    _ = Algebra.trace K L (x * algebraMap B L (b i)) *
          Algebra.trace K L (y i * algebraMap B L w) := by rw [ha i]
  have htrace :
      Algebra.trace K L (x * algebraMap B L (∑ i, a i • b i)) =
        Algebra.trace K L (x * algebraMap B L w) := by
    calc Algebra.trace K L (x * algebraMap B L (∑ i, a i • b i))
      = ∑ i, Algebra.trace K L (x * algebraMap B L (a i • b i)) := by
          simp only [map_sum, Finset.mul_sum]
    _ = ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) *
          Algebra.trace K L (y i * algebraMap B L w) :=
          Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = Algebra.trace K L ((∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i) *
          algebraMap B L w) := by
          simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
    _ = Algebra.trace K L (x * algebraMap B L w) := by rw [hsum x]
  rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, sub_eq_zero]
  exact htrace

omit [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L] in
/-- Action of `c : B` on `mulByTraceDualQuotientMap y hy q` under `traceDualQuotientMap`. -/
private theorem traceDualQuotientMap_smul_mulByTraceDualQuotientMap
    (y : L) (hy : y ∈ Submodule.traceDual A K (1 : Submodule B L)) (c : B)
    (a : A) (ha : algebraMap A K a = Algebra.trace K L (y * algebraMap B L c))
    (q : K ⧸ (1 : Submodule A K)) :
    traceDualQuotientMap A K B L (c • mulByTraceDualQuotientMap A K B L y hy q) = a • q := by
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [mulByTraceDualQuotientMap_mk, ← Submodule.Quotient.mk_smul, traceDualQuotientMap_mk,
    ← Submodule.Quotient.mk_smul]
  congr 1
  calc Algebra.trace K L (c • (k • y))
    = Algebra.trace K L (k • (y * algebraMap B L c)) := by
        rw [smul_comm, Algebra.smul_def c y, mul_comm _ y]
  _ = k * Algebra.trace K L (y * algebraMap B L c) := by rw [map_smul, smul_eq_mul]
  _ = a • k := by rw [← ha, mul_comm, ← Algebra.smul_def]

omit [IsDomain A] [IsFractionRing A K] in
/-- The `B`-linear trace-dual comparison map `L ⧸ Bᵛ →ₗ[B] Hom_A(B, K ⧸ A)`. -/
private def traceDualToPrecomp :
    (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) →ₗ[B]
      PrecompLinearMap A B (K ⧸ (1 : Submodule A K)) where
  toFun q := ⟨{
    toFun := fun b ↦ traceDualQuotientMap A K B L (b • q)
    map_add' := fun _ _ ↦ by rw [add_smul, map_add]
    map_smul' := fun a b ↦ by rw [RingHom.id_apply, smul_assoc, map_smul] }⟩
  map_add' _ _ := (PrecompLinearMap.equiv A B _).injective <| by
    ext b; simp [PrecompLinearMap.equiv, PrecompLinearMap.add_apply, smul_add]
  map_smul' b₁ q := (PrecompLinearMap.equiv A B _).injective <| by
    ext b₂
    change traceDualQuotientMap A K B L (b₂ • b₁ • q) =
      traceDualQuotientMap A K B L ((b₂ * b₁) • q)
    rw [mul_smul]

omit [IsDomain A] [IsFractionRing A K] in
/-- `traceDualToPrecomp` is invertible via any finite trace-dual family `(b, y)`. -/
private theorem traceDualToPrecomp_sum_mulBy {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (f : PrecompLinearMap A B (K ⧸ (1 : Submodule A K))) :
    traceDualToPrecomp A K B L
        (∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (f.toLinearMap (b i))) = f := by
  apply (PrecompLinearMap.equiv A B _).injective
  ext c
  have hmem (i : Fin n) :
      ∃ a : A, algebraMap A K a = Algebra.trace K L (y i * algebraMap B L c) := by
    simpa [Algebra.traceForm_apply, mul_comm (y i)] using
      Submodule.mem_traceDual.mp (hy i) (algebraMap B L c) (Submodule.mem_one.mpr ⟨c, rfl⟩)
  choose a ha using hmem
  have ha_sum : ∑ i, a i • b i = c := sum_smul_eq_of_dualFamily A K B L b y hsum c a ha
  calc (traceDualToPrecomp A K B L
        (∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (f.toLinearMap (b i)))).toLinearMap c
    = ∑ i, traceDualQuotientMap A K B L
        (c • mulByTraceDualQuotientMap A K B L (y i) (hy i) (f.toLinearMap (b i))) := by
        change traceDualQuotientMap A K B L (c • ∑ i, _) = _
        simp only [Finset.smul_sum, map_sum]
  _ = ∑ i, a i • f.toLinearMap (b i) :=
        Finset.sum_congr rfl fun i _ ↦
          traceDualQuotientMap_smul_mulByTraceDualQuotientMap A K B L
            (y i) (hy i) c (a i) (ha i) _
  _ = f.toLinearMap (∑ i, a i • b i) := by simp only [map_sum, map_smul]
  _ = f.toLinearMap c := by rw [ha_sum]

section FiniteProjective

variable [Module.Finite A B] [Module.Projective A B]

/-- Trace-specific `B`-linear equivalence `L ⧸ Bᵛ ≃ₗ[B] Hom_A(B, K ⧸ A)`. -/
private def traceDualQuotientEquiv :
    (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) ≃ₗ[B]
      PrecompLinearMap A B (K ⧸ (1 : Submodule A K)) :=
  LinearEquiv.ofBijective (traceDualToPrecomp A K B L) <| by
    obtain ⟨n, b, y, hy, hsum⟩ := exists_sum_trace_mul_smul_eq A K (B := B) (L := L)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun f ↦ ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (f.toLinearMap (b i)),
        fun q ↦ ?_, traceDualToPrecomp_sum_mulBy A K B L b y hy hsum⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hbi (i : Fin n) :
        traceDualQuotientMap A K B L (b i • Submodule.Quotient.mk x) =
          Submodule.Quotient.mk (Algebra.trace K L (x * algebraMap B L (b i))) := by
      rw [← Submodule.Quotient.mk_smul, traceDualQuotientMap_mk, Algebra.smul_def, mul_comm]
    change ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i)
      (traceDualQuotientMap A K B L (b i • Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    simp only [hbi, mulByTraceDualQuotientMap_mk]
    simp_rw [← Submodule.mkQ_apply]
    rw [← map_sum, hsum x]

/-- **Inverse-different trace comparison for linear maps**: when `B` is finite projective over `A`,
postcomposition with `traceDualQuotientMap` gives `(M →ₗ[B] (L ⧸ Bᵛ)) ≃ₗ[A] (M →ₗ[A] (K ⧸ A))`. -/
def traceDualLinearMapEquiv (M : Type*) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] :
    (M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) ≃ₗ[A]
      (M →ₗ[A] (K ⧸ (1 : Submodule A K))) :=
  let e := traceDualQuotientEquiv A K B L
  let congrR :
      (M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) ≃ₗ[A]
        (M →ₗ[B] PrecompLinearMap A B (K ⧸ (1 : Submodule A K))) :=
    { toFun := fun φ ↦ e.toLinearMap ∘ₗ φ
      invFun := fun φ ↦ e.symm.toLinearMap ∘ₗ φ
      left_inv := fun φ ↦ LinearMap.ext fun m ↦ e.symm_apply_apply (φ m)
      right_inv := fun φ ↦ LinearMap.ext fun m ↦ e.apply_symm_apply (φ m)
      map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ map_add e _ _
      map_smul' := fun _ _ ↦ LinearMap.ext fun _ ↦ map_smul (e.restrictScalars A) _ _ }
  congrR.trans (coextendHomEquiv A B (K ⧸ (1 : Submodule A K)) M)

@[simp] theorem traceDualLinearMapEquiv_apply {M : Type*} [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M]
    (φ : M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) (m : M) :
    traceDualLinearMapEquiv A K B L M φ m = traceDualQuotientMap A K B L (φ m) := by
  change traceDualQuotientMap A K B L ((1 : B) • φ m) = traceDualQuotientMap A K B L (φ m)
  rw [one_smul]

/-- `traceDualLinearMapEquiv` is compatible with the `B`-module structure on `M`. -/
theorem traceDualLinearMapEquiv_smul_apply {M : Type*} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] (b : B)
    (φ : M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) (m : M) :
    traceDualLinearMapEquiv A K B L M (b • φ) m = traceDualLinearMapEquiv A K B L M φ (b • m) := by
  simp [traceDualLinearMapEquiv_apply, map_smul]

/-- Explicit formula for `(traceDualLinearMapEquiv).symm` via any finite trace-dual family. -/
theorem traceDualLinearMapEquiv_symm_apply_of_dualFamily {M : Type*} [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (ψ : M →ₗ[A] (K ⧸ (1 : Submodule A K))) (m : M) :
    (traceDualLinearMapEquiv A K B L M).symm ψ m =
      ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m)) := by
  let f : PrecompLinearMap A B (K ⧸ (1 : Submodule A K)) :=
    (coextendHomEquiv A B (K ⧸ (1 : Submodule A K)) M).symm ψ m
  have hf :
      traceDualQuotientEquiv A K B L
          (∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m))) = f :=
    traceDualToPrecomp_sum_mulBy A K B L b y hy hsum f
  have hsymm :
      (traceDualQuotientEquiv A K B L).symm f =
        ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m)) :=
    (traceDualQuotientEquiv A K B L).symm_apply_eq.mpr hf.symm
  exact hsymm

end FiniteProjective

end TraceDualEquiv

section PrincipalDifferent

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

/-- With `A` integrally closed and `B` a Dedekind domain, when
`differentIdeal A B = Ideal.span {δ}`, dividing by `δ` induces a `B`-linear equivalence
`(L ⧸ B) ≃ₗ[B] (L ⧸ Bᵛ)`. -/
def quotientEquivTraceDualQuotientOfDifferentIdealEqSpan {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) :
    (L ⧸ (1 : Submodule B L)) ≃ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) :=
  let u : Lˣ := Units.mk0 (algebraMap B L δ)
    (algebraMap_ne_zero_of_differentIdeal_eq_span (R := A) (K := K) (L := L) hδ)
  Submodule.Quotient.equiv _ _ (u.mulRightLinearEquiv B).symm <| by
    ext y
    rw [Submodule.mem_map_equiv, mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ]
    simp [u]
@[simp] theorem quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (x : L) :
    quotientEquivTraceDualQuotientOfDifferentIdealEqSpan A K B L hδ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x / algebraMap B L δ) := by
  simp [quotientEquivTraceDualQuotientOfDifferentIdealEqSpan, div_eq_mul_inv]
@[simp] theorem quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_symm_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (x : L) :
    (quotientEquivTraceDualQuotientOfDifferentIdealEqSpan A K B L hδ).symm
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x * algebraMap B L δ) := (rfl)

end PrincipalDifferent

section DirectTrace

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K] [IsIntegrallyClosed A] [IsIntegralClosure B A L] [FiniteDimensional K L]

/-- The direct `A`-linear trace map `L ⧸ B → K ⧸ A`, descending from `Algebra.trace K L`. -/
def directTraceQuotientMap : (L ⧸ (1 : Submodule B L)) →ₗ[A] (K ⧸ (1 : Submodule A K)) :=
  (traceDualQuotientMap A K B L).comp
    ((Submodule.factor Submodule.one_le_traceDual_one).restrictScalars A)
@[simp] theorem directTraceQuotientMap_mk (x : L) :
    directTraceQuotientMap A K B L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Algebra.trace K L x) := (rfl)

/-- The direct trace pairing `L ⧸ B → (B →ₗ[A] (K ⧸ A))` sending `[x]` to `b ↦ [Tr_{L/K}(b x)]`. -/
def directTracePairing : (L ⧸ (1 : Submodule B L)) →ₗ[A] (B →ₗ[A] (K ⧸ (1 : Submodule A K))) where
  toFun q :=
    { toFun := fun b ↦ directTraceQuotientMap A K B L (b • q)
      map_add' := fun _ _ ↦ by rw [add_smul, map_add]
      map_smul' := fun _ _ ↦ by simp only [RingHom.id_apply, smul_assoc, map_smul] }
  map_add' _ _ := by ext; simp [smul_add, map_add]
  map_smul' a _ := by ext b; simp [smul_comm b a, map_smul]
@[simp] theorem directTracePairing_mk_apply (x : L) (b : B) :
    directTracePairing A K B L (Submodule.Quotient.mk x) b =
      Submodule.Quotient.mk (Algebra.trace K L (algebraMap B L b * x)) := by
  dsimp only [directTracePairing, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Submodule.Quotient.mk_smul, directTraceQuotientMap_mk, Algebra.smul_def]

/-- An element `[x] ∈ L ⧸ B` lies in the kernel of `directTracePairing` if and only if `x ∈ Bᵛ`. -/
theorem mem_ker_directTracePairing_iff (x : L) :
    Submodule.Quotient.mk (p := (1 : Submodule B L)) x ∈
        LinearMap.ker (directTracePairing A K B L) ↔
      x ∈ Submodule.traceDual A K (1 : Submodule B L) := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff, Submodule.mem_traceDual]
  refine ⟨fun h y hy ↦ ?_, fun h b ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hy
    simpa [Algebra.traceForm_apply, mul_comm, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one] using h b
  · simpa [Algebra.traceForm_apply, mul_comm, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one] using h (algebraMap B L b) (Submodule.mem_one.mpr ⟨b, rfl⟩)

/-- **Kernel of the naive trace pairing**: `ker(L ⧸ B → Hom_A(B, K ⧸ A))` is precisely the image
of the inverse different `Bᵛ` in `L ⧸ B`. -/
theorem ker_directTracePairing :
    LinearMap.ker (directTracePairing A K B L) =
      ((Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A).map
        ((1 : Submodule B L).mkQ.restrictScalars A) := by
  let f := (directTracePairing A K B L).comp ((1 : Submodule B L).mkQ.restrictScalars A)
  have hker :
      LinearMap.ker f = (Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A := by
    ext x
    exact mem_ker_directTracePairing_iff A K B L x
  have hle : (1 : Submodule B L).restrictScalars A ≤ LinearMap.ker f := by
    rw [hker]
    exact Submodule.one_le_traceDual_one
  have hlift : ((1 : Submodule B L).restrictScalars A).liftQ f hle =
      (directTracePairing A K B L :
        (L ⧸ (1 : Submodule B L).restrictScalars A) →ₗ[A] _) :=
    LinearMap.ext fun q ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rfl
  have hq := Submodule.ker_liftQ ((1 : Submodule B L).restrictScalars A) f hle
  rw [hlift, hker] at hq
  exact hq

/-- The direct trace pairing `L ⧸ B → Hom_A(B, K ⧸ A)` is injective iff `Bᵛ = B`. -/
theorem ker_directTracePairing_eq_bot_iff :
    LinearMap.ker (directTracePairing A K B L) = ⊥ ↔
      Submodule.traceDual A K (1 : Submodule B L) = 1 := by
  rw [ker_directTracePairing, eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  exact ⟨fun h ↦ le_antisymm h Submodule.one_le_traceDual_one, fun h x hx ↦ h ▸ hx⟩

/-- Over a Dedekind domain `B`, `directTracePairing` is injective iff `differentIdeal A B = ⊤`. -/
theorem ker_directTracePairing_eq_bot_iff_differentIdeal_eq_top
    [IsDomain A] [Algebra.IsSeparable K L] [IsDedekindDomain B] [Module.IsTorsionFree A B] :
    LinearMap.ker (directTracePairing A K B L) = ⊥ ↔ differentIdeal A B = ⊤ := by
  rw [ker_directTracePairing_eq_bot_iff]
  refine ⟨fun h ↦ eq_top_iff.mpr fun y _ ↦ ?_,
    fun h ↦ le_antisymm (fun x hx ↦ ?_) Submodule.one_le_traceDual_one⟩
  · rw [mem_differentIdeal_iff_forall_mem_traceDual (R := A) (K := K) (L := L), h]
    rintro _ hx; obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hx
    exact Submodule.mem_one.mpr ⟨b * y, map_mul (algebraMap B L) b y⟩
  · simpa using (mem_traceDual_one_iff_forall_mem_differentIdeal (R := A) (K := K)).mp hx
      1 (h.symm ▸ Submodule.mem_top)

end DirectTrace

end TauCeti
