use criterion::{criterion_group, criterion_main, Criterion};
use jsmn::{JsonParser, Kind, Token};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("twitter", |b| {
        let data = include_bytes!("../testdata/twitter.json");

        b.iter(|| {
            let mut parser = JsonParser::default();
            let mut tokens = Vec::new();
            tokens.resize(27259, Token::new(Kind::Str, 0, 0));

            parser.parse(data, &mut tokens).unwrap();
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
