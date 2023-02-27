use criterion::{criterion_group, criterion_main, Criterion};
use jsmn::{JsonParser, Token};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("twitter", |b| {
        let data = include_str!("../testdata/twitter.json");

        b.iter(|| {
            let mut parser = JsonParser::new();
            let mut tokens = Vec::new();
            tokens.resize(27259, Token::default());

            parser.parse(data.as_bytes(), &mut tokens).unwrap();
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
